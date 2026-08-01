# HAETAE Reference EasyCrypt Verification

This workspace is intended to connect the provable-security argument in the
HAETAE specification to the actual Jasmin implementation in
`../haetae-ref-jasmin`.

The work is deliberately split into two proof layers:

1. prove that the target Jasmin key-generation, signing, and verification
   procedures refine a paper-faithful HAETAE model; and
2. prove the security bound for that model and compose the results.

A passing KAT, a successful Jasmin extraction, functional correctness, and
cryptographic security are separate claims. See
[`docs/00-scope-and-claims.md`](docs/00-scope-and-claims.md) for the claim and
trust boundaries.

## Status

Phases 0 and 1 are complete. Phase 2 has begun, with the target NTT extraction
and single-polynomial mathematical refinement,
standalone FIPS202/SHAKE, mode-2 key-generation seed-XOF, mode-2 uniform-XOF,
mode-2 eta-XOF, unified key-generation sampler-caller extraction, and the
actual deterministic mode-2 key-generation parent extraction and proof-only
parent-module sampler-prefix refinement submilestones complete. A separate
proof surface now gives the actual extracted `_kp_m23_matrix` helper its
fixed-mode algebraic semantics and totality theorem, gives the actual mode-2
finalizer exact word semantics, canonical reduction, abstract HAETAE
coefficient decomposition, and totality, and composes these after the checked
sampler in a proof-only observer. The actual fixed-parameter `_singular_full`
now has an exact `W32`/`W64` evaluator and a totality theorem covering the
bit-reversal initialization, all eight FFT stages, five squared-magnitude
accumulations, and the five-entry finish computation. A separate numerical
boundary proves the exact Q16 multiplication decoder under its signed-fit
premise, names the remaining overflow obligations, and proves that a zero
256-word accumulator produces score `120` through the implementation's actual
selector and finish pipeline rather than the paper's fixed-weight score
`256`. A new analytic scaffold adds a transparent real-pair complex arithmetic
library, exact bit-reversal and signed root-table range facts for the extracted
constants, local signed-integer decoders for the Q16 butterfly and accumulator
kernels, and an already-selected equal-value finish regression whose
implementation and paper scores fall on opposite sides of the mode-2 guard.
The analytic layer now also constructs a lower-half-plane 512th root from
proved real square roots, checks its dyadic primitivity criterion, defines the
abstract 256-point odd-root DFT, and proves its coefficient-twist identity
without a project-authored axiom. A pure exact-complex schedule theorem now
proves that bit reversal followed by all eight radix-2 stages computes the
defined `dft256`, and that twisting its input computes `odd_dft256`.
Three checked certificate theories now prove that every signed coordinate in
the extracted `jfft_roots` table is the unique nearest Q16 encoding of the
corresponding exact `ideal_root j` coordinate, with strict error below
`1/131072`. A decoded initialization bridge now proves all 256 complex-cell
updates (512 word stores) and frames, discharges their signed products under
coefficient magnitude at most two, and bounds the initialized vector within
`1/65536` of the exact bit-reversed twisted input. A one-butterfly bridge now
identifies all four target stores, both decoded destinations, and every framed
cell, and proves `1/65536` local rounding error under the explicit signed-safe
contract. An exact `k`-prefix bridge lifts those destination and frame facts
through any valid inner-loop prefix under safety premises evaluated on each
evolving pre-step machine state. Its observer deliberately retains the rounded
Q16 butterfly surface. An exact block-prefix bridge now composes complete inner
loops through any valid block prefix under safety evaluated on each exact
evolving pre-block state. The proof still does not lift through a complete
stage, establish an eight-stage safe trace, or prove global FFT/accumulator
error and nonoverflow.
A fixed-mode relational
theorem peels the mandatory first iteration of the actual
`_keypair_full_m23` into a result-carried mirror, proves equality of the final
packed key arrays, and records that evaluator result together with the exact
sampler, M23, finalizer, canonical, HAETAE, counter, and unsigned-guard facts
while retaining the residual retry loop and both packing calls. It does not
prove first-attempt acceptance, residual-loop termination, an analytic
real/spectral interpretation of the machine FFT and score, or packing
correctness. The specification
and target implementation inputs are fingerprinted, the security
declaration and theorem-premise surfaces are classified, every paper-gap row
has a planned owner lemma and acceptance criterion, and seven focused
EasyCrypt extraction surfaces are reproducibly generated from the exact target
Jasmin sources. The authored sampler proof
layer proves schedule-level relational equivalence for the three callers,
checked integer/`W64` schedule facts, finite uniform-consumer coefficient
bounds and frames, partial-correctness range/frame contracts for both whole
uniform leaves, exact centered-residue helper arithmetic, and exact eta
decoder/consumer contracts in addition to the eta counter, centered-interval,
and frame contracts. The centered-range, frame, and exact finite-stream
invariants are lifted through the whole eta leaf and the actual generated eta
vector caller for every nonnegative capacity-safe count (necessarily at most
eight polynomials). `eta_vector_stream8192` gives each slot its own finite
SHAKE256 block witness at seed offset 32 and nonce `start + slot`;
`expand_eta_stream` proves that predicate for `_kp_polyvec_expand_eta`. The
authored proof-only `CheckedMode2EtaPair.expand` wrapper composes two invocations
of that actual generated caller with mode-2 counts three and two over the same
input seed array. It is not the extracted `_keypair_full_m23`. The proof layer
also proves the exact target-functional framing performed by the specialized
SHAKE128 and SHAKE256 initializers: a zero state absorbs respectively 32 or 64
seed bytes and two little-endian nonce bytes before the domain separator and
final rate bit are set. The two squeeze procedures are proved to serialize
exactly 168 or 136 bytes from their returned permutation state and to preserve
the output buffer outside that block. The generated `_keccakf1600` wrapper is
proved to realize the exact 24-round Keccak-f[1600] transition under the
25-lane `W64` representation. A checked byte/lane bridge identifies the raw
200-byte states with the pinned Keccak model, and the framed initializer states
with the exact one-block `seed || nonce_le16` padding states. Capacity-bounded
proof wrappers call one actual extracted initializer followed by `n` actual
extracted squeeze calls. They prove that the final state is the `n`-fold Keccak
byte transition from the padded state, that each retained consecutive 168-byte
or 136-byte block is the corresponding post-permutation rate prefix, and that
every byte outside the total output interval is preserved.
`kp_expand_seedbuf_correct` uses the same pinned model to prove that the actual
unified generated seed-expansion procedure returns exactly the first 128 bytes
of SHAKE256 on its 32-byte seed. The proof fixes the domain byte at state byte
32, the final rate bit at byte 135, the one Keccak-f[1600] call, and every byte
written by the output loop. Its three named Hoare corollaries expose the
uniform seed slice `[0, 32)`, eta seed slice `[32, 96)`, and key slice
`[96, 128)`.
`shake128_seedbuf_four_blocks` specializes this wrapper to four blocks at
offset zero. Both actual uniform leaves now carry the same exact state-and-byte
account through their complete rejection loops. Under an in-bounds 32-byte seed
slice, the first four squeezes produce the exact four-step state and flat
672-byte FIPS prefix. `consume2048_first672` and `consume8192_first672` connect
that prefix to the actual little-endian decoder and strict `< 64513` guard.
`consume2048_block168` and `consume8192_block168` then extend any exact decoded
prefix with the accepted values from an exact 168-byte continuation block. The
checked loop invariant keeps `buflen = 672` at the initial loop entry and
`buflen = 168` thereafter. Both are even, so the generated
`off = buflen & 1` is zero, the carry-copy loop is empty, and each later actual
squeeze supplies exactly the next SHAKE128 block at offset zero.

The exported `uniform2048_leaf_stream` and `uniform8192_leaf_stream` Hoare
theorems give the resulting finite decoded-prefix postcondition. Conditional on
the seed-slice bound, if a leaf terminates, there are `blocks >= 4` and
`0 <= pairs <= 84 * blocks` such that the accepted values among the first
`pairs` little-endian candidates of the exact `blocks`-block SHAKE128 byte
sequence have size 256 and equal the stored output prefix in order. Separate
whole-leaf theorems preserve the destination frame. SHAKE256 is specialized from
the pinned `HAETAE_FIPS202` model; SHAKE128 uses the analogous short-message
construction over the same pinned Keccak model.

`uniform_consume2048_ll` and `uniform_consume8192_ll` prove unconditional
termination of the bounded generated consumers. Separately,
`uniform2048_leaf_progress_ll` and `uniform8192_leaf_progress_ll` prove
probability-one termination of the two actual whole leaves when the concrete
seed, offset, nonce, destination bounds, and an explicit finite
`uniform_progress_prefix` certificate are supplied. That deterministic
certificate has a finite endpoint with at least 256 accepted candidates and
requires strict accepted-count progress at every still-incomplete full-block
prefix from block four to that endpoint. It is not proved for every input and
does not establish either uniform caller's termination or a distribution.

The same finite SHAKE128 semantics are now lifted through both actual generated
uniform callers. `expand_vecA_stream_correct` covers every `k <= 8` vector slot,
and `expand_matA_stream_correct` covers every matrix cell under
`rows * cols <= 32`. Each slot or cell retains its own `blocks` and `pairs`
witnesses, exactly 256 accepted values below 64513, and equality with its stored
prefix. Both theorems also give aggregate byte frames outside the complete
selected output prefix. `caller_uniform_values` fixes seed offset zero and the
generated nonce word. The named input lemmas prove that bytes 0 through 31 are
the same raw `BArray128` prefix and that the mode-2 little-endian nonce tails are
`[col, row]` for the matrix and `[3 + slot, 2]` for the vector. The authored
proof-only `CheckedMode2UniformPair.expand` wrapper composes the actual matrix
and vector callers with dimensions `(2, 3)` over that same raw input array.

The eta specification maps each byte below 243 to its five centered base-three
digits in low-to-high order and maps every rejected byte to the empty list.
`eta_consume2048_block136` proves that the generated consumer applies exactly
that decoder to one 136-byte block and caps the accumulated list at 256,
including truncation in the middle of an accepted byte's five digits.
`eta2048_leaf_stream` connects the exact padded SHAKE256 seed/nonce state and
each successive offset-zero 136-byte overwrite squeeze to this decoder. Under
the theorem's 64-byte seed-slice and destination-capacity bounds, a terminating
leaf stores exactly the resulting 256-value finite prefix. `expand_eta_stream`
lifts this result through the actual generated `_kp_polyvec_expand_eta`: every
selected slot has its own terminating finite-block witness, uses the caller's
shared seed array at offset 32, and uses nonce `start + slot`. The proof-only
`checked_mode2_eta_pair_correct` theorem composes count-three and count-two
caller invocations, their five-slot word-nonce schedule, and the returned nonce
word `start + 5`. These are ordinary
Hoare partial-correctness results. Separately, `eta_consume2048_ll` proves
unconditional termination of the bounded eta consumer, and
`eta2048_leaf_progress_ll` proves probability-one termination of the actual eta
leaf when the concrete seed, offset, nonce, destination bounds, and an explicit
finite `eta_progress_prefix` certificate are supplied. No theorem proves that
either progress certificate exists for every input, an unconditional
whole-leaf or caller losslessness claim, uniformity or another distributional
property, or an arbitrary infinite-stream theorem. The uniform and eta caller
theorems used by the earlier proof-only pairs establish only raw-array-relative
inputs. The later `CheckedMode2ParentSamplerPrefix.run` observer closes that
raw-array gap for one proof-only prefix: it calls the actual parent module's
`_kp_expand_seedbuf`, matrix and vector uniform callers, and two first-attempt
eta callers over the same expanded array. Its Hoare theorem carries the exact
seed identity and slice facts into the caller postconditions. The observer
stops before `_kp_m23_matrix` and is not `_keypair_full_m23`.

`CheckedMode2ParentM23Finalize.run` extends that sampler result in a separate
proof-only observer. The actual fixed `(2, 3)` `_kp_m23_matrix` theorem
composes the exact copy, three forward NTTs, two exact three-column Montgomery
rows, and two inverse NTTs, with active-region bounds, frames, and
probability-one termination. The actual `_keypair_finalize_m23` theorem fixes
the mode-2 count at 512 and gives exact word-level outputs for both arrays,
both tail frames, and helper totality. The combined observer preserves the
sampler and M23 facts and adds the exact finalizer output. The strengthened
semantic theorem derives the signed-18-bit freeze premise from those facts,
proves canonical reduction modulo `64513`, and identifies all 512 high/low
and adjusted-`s2` coefficient equations with the definitions in
`HAETAE_Algebra`. Its progress theorem remains conditioned on the
sampler-prefix certificate.

`TargetKeygenM23FullFirstAttempt` connects this observer to the actual
fixed-parameter `_keypair_full_m23` through a result-carried mirror. Its
equivalence theorem preserves the final packed outputs while peeling the
unconditional first loop iteration; the mirror retains the unchanged retry
tail and both packing calls. Its immutable trace has the exact sampler, M23,
word-level finalizer, canonical, and HAETAE pointwise facts, counter `5`,
the exact fixed-mode `_singular_full` word evaluator, protected bound
`611098`, and exact unsigned rejection guard. The guard is also characterized
as `W64.to_uint(score) <= 611098`. This is not a proof that the first attempt
accepts, that the residual retry loop terminates, that the machine FFT and
score equal an intended real or spectral singular-value construction, or that
packing has its intended mathematical meaning.
The target NTT/matrix representation-to-list multiplication bridge,
source-pointer safety, distributions, and identity with paper rho/`seedA` and
sigma/`seedsk` also remain open.
Current limitations are recorded in
[`docs/proof-status.md`](docs/proof-status.md) and
[`docs/02-existing-proof-audit.md`](docs/02-existing-proof-audit.md). The
security dependency chain is detailed in
[`docs/03-security-premise-audit.md`](docs/03-security-premise-audit.md).
The singular numerical boundary is detailed in
[`docs/15-target-keygen-singular-numeric-boundary.md`](docs/15-target-keygen-singular-numeric-boundary.md).

The full roadmap is in [`PLAN.md`](PLAN.md).

## Initial checks

Verify that the pinned specification, imported security model, Jasmin sources,
and KAT files have not changed:

```sh
cd haetae-ref-easycrypt
./scripts/check-sources.sh
```

Re-run the existing implementation, security-proof, and NTT-proof baselines:

```sh
cd haetae-ref-easycrypt
./scripts/verify-baselines.sh
```

These commands reproduce existing evidence. They do not yet prove that the
complete `haetae-ref-jasmin` implementation is functionally equivalent to the
security model.

Verify the extraction generated from the actual target NTT source:

```sh
cd haetae-ref-easycrypt
./scripts/verify-ntt-extract.sh
```

Verify the mathematical refinement of the exact target NTT procedures:

```sh
cd haetae-ref-easycrypt
./scripts/verify-ntt-proof.sh
```

This gate proves the current extracted scalar Montgomery multiplication and
single-polynomial forward/inverse NTTs against the checked algebraic
specification. It does not yet lift that result to the wide-array vector loops
or pointwise accumulator used by `_kp_m23_matrix`; the separate mode-2 M23
gate below performs that fixed-mode lifting.

Verify the standalone one-shot SHAKE extraction generated from the target
FIPS202 and Keccak sources:

```sh
cd haetae-ref-easycrypt
./scripts/verify-fips202-shake-extract.sh
```

This SHAKE extraction is a primitive foothold. The mode-2 key-generation,
signing, and verification paths use specialized Keccak routines, so the
standalone wrappers do not by themselves establish those call-path
transcripts.

Verify the first exact SHAKE leaf reachable from mode-2 key generation:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-seed-xof-extract.sh
```

This command establishes the focused extraction provenance for
`_kp_expand_seedbuf`. The unified authored proof below separately establishes
that its generated copy returns exactly `SHAKE256(seed, 128)`, including named
corollaries for byte intervals `[0, 32)`, `[32, 96)`, and `[96, 128)`.

Verify the two exact SHAKE128 rejection-sampler leaves reachable from mode-2
key generation:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-uniform-xof-extract.sh
```

This establishes reproducible extraction of the two memory-specialized leaf
kernels. It does not prove SHAKE128 correctness, uniform output distribution,
termination, memory safety, or the caller-level mode-2 nonce schedule.

Verify the exact SHAKE256 eta-sampler leaf reachable from mode-2 key
generation:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-eta-xof-extract.sh
```

This establishes reproducible extraction of the 2048-word memory-specialized
leaf. It does not prove SHAKE256 correctness, centered-trit uniformity,
termination, memory safety, or caller-level seed and nonce composition.

Verify the unified seed-expansion and parameterized sampler-caller layer:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-sampler-callers-extract.sh
```

This establishes reproducible extraction of `_kp_expand_seedbuf`, the matrix,
`agen`, and eta caller loops together with their leaf closures: exactly 25
generated files and 31 procedures. It does not by itself prove their functional
contracts or compose their parameters and retry schedule in the actual mode-2
parent.

Verify extraction of the actual deterministic mode-2 key-generation parent:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-mode2-parent-extract.sh
```

This checks a 32-file, 56-procedure closure rooted at
`crypto_sign_keypair_internal_mode2_jazz`, including `_keypair_full_m23`, with
zero regeneration drift and `-no-eco` compilation. It is extraction-only
evidence: it does not prove a semantic parent theorem, retry termination,
source-pointer safety, or end-to-end refinement. See
[`docs/12-target-keygen-mode2-parent-extraction.md`](docs/12-target-keygen-mode2-parent-extraction.md).

Verify the authored sampler-consumer and caller refinement:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-sampler-callers-proof.sh
```

The gate checks the pinned sources and extraction drift, then compiles the
generated target, six authored specifications, and six authored refinements:
a 13-entry `-no-eco` proof surface. It rejects
`admit`/`abort` proof commands and axiom declarations. The checked contracts
cover caller schedules, finite uniform-consumer accepted-prefix bounds and
frames, whole uniform-leaf range/frame partial correctness, centered-residue
helpers, eta-consumer and whole-leaf centered-range/frame behavior, the
capacity-safe uniform matrix and vector callers' exact per-cell SHAKE128
decoded prefixes, coefficient ranges, and aggregate byte frames, the
capacity-safe eta vector caller's centered range, outside-vector frame, and
exact per-slot SHAKE256 decoded prefixes, the authored proof-only mode-2
uniform and eta pair wrappers, and the exact target-functional
SHAKE128/SHAKE256 initializer framing. They also cover the generated
permutation's exact 24-round transition under the abstract
25-lane representation and exact one-call little-endian serialization of its
returned state, including the output-buffer frame. The byte/lane adapter,
short-message padding states, and capacity-bounded consecutive-block
SHAKE128/SHAKE256 compositions are also checked. The bounded consumers have
unconditional losslessness theorems, and all three actual leaf variants have
probability-one termination theorems under their exact deterministic progress
certificates and memory/slice preconditions. The current authored uniform
proofs additionally cover the exact four-call SHAKE128 prelude, its first
consumer, exact 168-byte continuation consumers, and the real enclosing loops.
Their reachable even-`buflen` invariant forces every later syntactic
parity/carry offset to zero and connects each actual squeeze to the next
abstract SHAKE128 block. Conditional `uniform2048_leaf_stream` and
`uniform8192_leaf_stream` postconditions expose the final 256-value decoded
prefix from a finite exact byte sequence. `expand_vecA_stream_correct` and
`expand_matA_stream_correct` lift those exact finite witnesses through the two
actual generated uniform callers while preserving prior regions, coefficient
bounds, and aggregate output frames. The mode-2 raw-input lemmas expose the
common seed bytes at offset zero and the exact two-byte nonce tails, while
`checked_mode2_uniform_pair_correct` composes both callers over the same raw
array inside an authored proof-only wrapper. The eta proof similarly follows the
generated offset-zero SHAKE256 overwrite loop. `eta_consume2048_block136`
implements strict `< 243` rejection, emits five centered trits per accepted
byte, and applies the 256-value cap exactly even when it truncates the last
accepted byte. Conditional `eta2048_leaf_stream` connects successive exact
136-byte SHAKE256 blocks to the generated 2048-word leaf's stored prefix.
`expand_eta_stream` carries per-slot finite-block witnesses through the
actual generated eta vector caller while preserving earlier polynomial
prefixes. `checked_mode2_eta_pair_correct` then composes two actual caller
invocations inside an authored proof-only wrapper, with one input seed array,
counts three and two, and five consecutive word-nonce slots. The proof manifest
also includes the exact seed-XOF specification and refinement. The gate checks
64 pinned inputs, the unified 25-file, 31-procedure extraction, all 13 proof
artifacts, proof-hole absence, and axiom-declaration absence; its retained
2026-07-22 result is written to
`logs/keygen-sampler-callers-proof-summary.txt` and ends with
`RESULT: PASS compiled=13 total=13 mode=-no-eco`. The
focused uniform caller layer adds the two generated-caller contracts, exact
mode-2 raw-input identities, and the proof-only shared-seed pair. These results
do not by themselves establish caller termination, a sufficient progress
certificate for every input, an arbitrary infinite stream, or any
distribution. The separate parent-module proof below lifts explicit endpoint
maps through the exact mode-2 callers and proof-only prefix. The bounded
consumers terminate unconditionally; both actual uniform leaves and the actual
eta leaf terminate with probability one under their respective explicit
deterministic progress certificates. These are not universal or distributional
claims. Source-pointer safety and a complete semantic refinement of the actual
`_keypair_full_m23` remain open. The later proof-only prefix closes the exact
expanded-seed identity only within that observer; it and the earlier pairs do
not establish singular-value rejection. The separate M23 gate below extends a
new proof-only observer through the exact word-level `egen - b0` adjustment,
and the M23 gate now derives its pointwise abstract HAETAE coefficient
semantics from the retained sampler and arithmetic bounds.
See
[`docs/10-target-keygen-sampler-callers-refinement.md`](docs/10-target-keygen-sampler-callers-refinement.md)
and
[`docs/11-target-keygen-sampler-consumers.md`](docs/11-target-keygen-sampler-consumers.md).

Reproduce the actual parent-module sampler-prefix refinement:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-mode2-parent-proof.sh
```

This gate checks both extraction surfaces and their 24 byte-identical shared
generated theories, then compiles the 17-entry proof manifest with `-no-eco`.
The retained 2026-07-23 run passes all 17 entries, the proof-hole scan, and the
axiom-declaration scan.
Seven pRHL bridges qualify the existing seed, caller, and leaf theorems for
`KeygenMode2ParentTarget.M`. Exact mode-2 certificate bundles cover six matrix
uniform calls, two vector uniform calls, and five first-attempt eta calls,
universally tied to the exact SHAKE256-expanded seed. The resulting authored
observer has exact finite-stream/range/frame partial correctness.
`checked_mode2_parent_sampler_prefix_progress_ll` separately proves its
probability-one termination under that explicit deterministic bundle. The
sampler-only observer is not `_keypair_full_m23` and stops before downstream
matrix, finalization, singularity, and packing. The separate M23 gate below
extends a proof-only composition through the actual matrix helper and exact
word-level finalizer, then relates the actual fixed-mode `_keypair_full_m23`
to a result-carried mirror with an immutable first-attempt trace and identical
final packed outputs. Outer retry acceptance or termination, universal
certificate existence, sampler distributions, source-pointer safety, and
security composition remain open. See
[`docs/13-target-keygen-mode2-parent-refinement.md`](docs/13-target-keygen-mode2-parent-refinement.md).

Verify the mode-2 M23 arithmetic, exact word finalization, and canonical
HAETAE coefficient bridge, exact fixed-mode singular-word evaluator,
extracted-root Q16 certificate, and first-attempt guard:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-m23-matrix-proof.sh
```

This gate checks the pinned sources; zero drift for the actual-parent,
sampler-caller, and target-NTT extractions; the project-owned NTT loop support;
and the 17 remaining imported NTT support
hashes. Its current summary passes all 39 authored
theories with `-no-eco` and the proof-hole, authored-axiom, and debug-command
scans. The theorem surface covers the exact copy and frames, active-prefix
scratch independence, the actual fixed `(2, 3)` helper's NTT and exact
three-column Montgomery arithmetic, and probability-one helper termination.
It also proves the actual 512-word `_keypair_finalize_m23` helper's exact word
outputs, both tail frames, and losslessness, then composes the checked sampler,
actual M23 helper, and actual finalizer in a proof-only observer. The final
proof layers give the actual fixed `(3, 2, 5, 58, 24)` `_singular_full` call
an exact word evaluator and totality theorem, then peel the first actual
`_keypair_full_m23` iteration into a result-carried mirror, identify its score
with that evaluator, prove the exact unsigned-bound characterization, preserve
equality of the eventual packed outputs, and retain the residual retry loop
plus both packing calls. The numerical boundary additionally proves the local
Q16 decoder under explicit fit premises, records the signed range obligations,
decodes the local scalar butterfly and accumulator kernels, checks the
tied-zero selector-and-finish implementation score `120` against the paper's
fixed-weight score `256`, and proves a separate equal-value finish regression
with implementation score `375000` and paper score `800000` around the
machine bound `611098`. The extracted constants also have exact 8-bit
bit-reversal contents and signed Q16 coordinate bounds, and a transparent
real-pair complex theory supplies the algebra and coordinate-error laws for
the later analytic proof. The ideal layer separately proves that the pure
exact-complex bit-reversed eight-stage schedule computes `dft256`, and that
the twisted-input schedule computes `odd_dft256`. The extracted-root
certificate additionally proves all 256 actual root pairs have the unique
nearest Q16 coordinates of that exact schedule, with strict per-coordinate
error below `1/131072`. The decoded initializer theorem additionally proves
the complete target write permutation, initialization signed safety under the
explicit coefficient bound two, and a whole-vector `1/65536` error bound
against the ideal bit-reversed twisted input. The local butterfly theorem
identifies its four word stores and two decoded outputs, frames the other 254
cells, and bounds its Q16 arithmetic rounding by `1/65536` against the exact
decoded-root complex butterfly whenever `fft_butterfly_safe_at` holds.
The `k`-prefix theorem then proves exact pointwise decoded equality for every
valid inner-loop prefix: processed destinations expose the rounded result from
their exact pre-step prefix state, and every untouched cell retains its original
decoded value. Its safety premise is explicit and remains to be discharged on
the reachable stage trace. The block-prefix theorem composes complete inner
loops over any valid block prefix using a folded observer evaluated on each
exact evolving pre-block state. Its first-stage schedule certificate also
checks the reachable `m = 2`, `md2 = 1`, `stride = 256` case without bounding
the first unexecuted twiddle.

On the reachable 512-word path, the gate additionally proves the exact
`freeze_word` sequence is canonical reduction modulo `q` and the word-level
EGen operations equal the abstract HAETAE coefficient low/high decomposition.
It does not prove the remaining NTT-to-security-model multiplication bridge,
the butterfly stage/eight-round machine-schedule correspondence to the
ideal DFT or schedule-wide safety, global FFT error or accumulator
nonoverflow, first-attempt
acceptance, residual-loop termination, packing semantics, pointer aliasing or
separation safety, or full key-generation correctness. See
[`docs/14-target-keygen-m23-matrix.md`](docs/14-target-keygen-m23-matrix.md)
and
[`docs/15-target-keygen-singular-numeric-boundary.md`](docs/15-target-keygen-singular-numeric-boundary.md).
The incremental analytic surface and compatibility decision are recorded in
[`docs/16-target-keygen-singular-analytic-scaffold.md`](docs/16-target-keygen-singular-analytic-scaffold.md);
the constructive root and ideal transform milestone is detailed in
[`docs/17-target-keygen-ideal-root-dft.md`](docs/17-target-keygen-ideal-root-dft.md);
the exact-complex schedule theorem is detailed in
[`docs/18-target-keygen-ideal-fft-schedule.md`](docs/18-target-keygen-ideal-fft-schedule.md);
and the extracted-table rounding certificate is detailed in
[`docs/19-target-keygen-root-table-rounding.md`](docs/19-target-keygen-root-table-rounding.md).
The decoded initialization and ideal-input error bridge is detailed in
[`docs/20-target-keygen-fft-initialization-bridge.md`](docs/20-target-keygen-fft-initialization-bridge.md).
The exact one-butterfly and local rounding bridge is detailed in
[`docs/21-target-keygen-fft-butterfly-bridge.md`](docs/21-target-keygen-fft-butterfly-bridge.md).
The exact evolving-state inner-prefix bridge is detailed in
[`docs/22-target-keygen-fft-k-prefix-bridge.md`](docs/22-target-keygen-fft-k-prefix-bridge.md).
The exact evolving-state block-prefix bridge is detailed in
[`docs/23-target-keygen-fft-block-prefix-bridge.md`](docs/23-target-keygen-fft-block-prefix-bridge.md).

## Baseline inputs

- Specification: `../haetae-security/HAETAE_v260204.pdf`
- Jasmin implementation: `../haetae-ref-jasmin/jasmin/`
- Existing security proofs: `../haetae-security/provable-security/`
- Existing NTT proof method: `../haetae-ntt-verify/easycrypt-ct/`

The NTT proof method currently targets a different `hpoly.jazz`. Its theorem
must not be transferred to `haetae-ref-jasmin` without extraction from the
target source and a checked refinement or source-equivalence result.

## Repository policy

- Files under `easycrypt/extract/` are generated and must
  never be edited manually.
- All checked EasyCrypt targets must compile with `-no-eco`.
- `admit` and `abort` are forbidden in final checked targets.
- Every axiom and theorem premise must appear in
  [`manifests/assumptions.md`](manifests/assumptions.md).
- A claim is `VERIFIED` only when its exact source, theorem, command, and fresh
  evidence are recorded in
  [`manifests/traceability.csv`](manifests/traceability.csv).
