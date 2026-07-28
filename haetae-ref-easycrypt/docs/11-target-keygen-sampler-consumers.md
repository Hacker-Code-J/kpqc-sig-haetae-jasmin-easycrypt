# Target Key-Generation Sampler Consumer, Leaf, and Caller Contracts

## Verified claim

This milestone gives the rejection consumers used by the extracted
key-generation sampler callers checked deterministic boundary contracts,
lifts those contracts through both whole uniform leaves under Hoare partial
correctness, and records the exact target-functional SHAKE128/SHAKE256
initializer framing plus exact one-call 24-round lane-level Keccak-f
transitions and serialization/frame contracts for the two squeeze procedures.
It also composes a capacity-bounded number of actual squeeze calls after one
actual initializer and connects the exact finite SHAKE128 byte sequence to the
decoder through both real uniform-leaf loops. It lifts those exact finite
streams, coefficient ranges, and aggregate byte frames through both actual
generated uniform callers and composes their mode-2 dimensions over one shared
raw seed array in an authored proof-only wrapper. It connects successive exact
SHAKE256 overwrite blocks to the centered-trit decoder through the generated
eta leaf, lifts that result through the actual generated eta vector caller, and
composes two actual caller invocations in an authored proof-only mode-2 pair.
The bounded consumers terminate unconditionally. The two actual uniform leaves
and the actual eta leaf additionally terminate with probability one under their
respective explicit deterministic progress certificates and exact
memory/slice preconditions. A separate proof-only parent-module prefix lifts
exact endpoint maps through the six-cell matrix, two-slot vector, and two
first-attempt eta caller segments.
The same gate proves, as an ordinary Hoare result, that on return the extracted
`_kp_expand_seedbuf` output is the first 128 SHAKE256 bytes of its 32-byte seed
and identifies the three sampler/key slices. It does not prove actual
`_keypair_full_m23` semantics or keypair composition, a probabilistic sampler
distribution, or arbitrary infinite-stream correctness. The separate prefix
connects those exact slices to the mode-2 matrix, vector, and first-attempt eta
calls; see
[`13-target-keygen-mode2-parent-refinement.md`](13-target-keygen-mode2-parent-refinement.md).

For the two uniform consumers, the proofs establish that:

- writes are confined to the 256-word polynomial region beginning at `base`;
- every coefficient in the accepted prefix through the returned counter is
  represented by a `W32` value whose unsigned value is less than `q = 64513`,
  assuming the incoming prefix already has that property; and
- the contracts hold for both the `BArray8192` and `BArray32768` memory
  specializations used by the extracted callers.

The specialized `consume2048_first672` and `consume8192_first672` theorems
add an exact first-buffer contract. Given counter zero, buffer length 672, and
a buffer matching a 672-byte FIPS prefix, each ordinary Hoare theorem proves
that, on termination, there is a processed-pair count `k` with `0 <= k <= 336`.
The returned counter is the number of strict-`< 64513` little-endian 16-bit
candidates among the first `k` pairs and is at most 256; the output prefix
contains those accepted values in order; the prefix is bounded; bytes outside
the reserved 256-word polynomial are preserved; and the consumer stopped
because the counter reached 256 or `k = 336`. The frame does not characterize
the unwritten suffix inside the reserved polynomial.

The continuation theorems `consume2048_block168` and `consume8192_block168`
start from an exact decoded and bounded prefix whose length equals the incoming
counter. Given an exact 168-byte block, each theorem witnesses `0..84`
processed pairs and appends exactly their accepted values to that prefix. The
returned counter is the concatenated-list size and is at most 256; the decoded
and bounded prefix and destination frame are preserved; and the consumer stops
full or after all 84 pairs.

`uniform_consume2048_ll` and `uniform_consume8192_ll` separately prove that
both generated finite consumers terminate on every input. Their decreasing
variants count the remaining candidate pairs plus the explicit `live` stop
transition, so these losslessness facts require no acceptance or distribution
hypothesis. They do not imply that a whole rejection leaf obtains 256 accepted
values.

The corresponding whole uniform leaves have range and frame Hoare theorems and
the exported `uniform2048_leaf_stream` and `uniform8192_leaf_stream` theorems.
If a leaf terminates, its full 256-word prefix is bounded. Conditional on the
32-byte seed-slice bound, the stream theorem additionally witnesses
`blocks >= 4` and `0 <= pairs <= 84 * blocks` such that the accepted values
among the first `pairs` candidates of the exact finite SHAKE128 byte sequence
have size 256 and equal the stored decoded prefix. The frame is supplied by the
separate frame theorem. These are partial-correctness claims and do not
by themselves establish termination or a distribution.

`uniform2048_leaf_progress_ll` and `uniform8192_leaf_progress_ll` separately
prove probability-one termination of the two actual generated leaves when the
initial seed, seed offset, nonce, base, destination capacity, 32-byte slice
bound, and an explicit finite `uniform_progress_prefix` certificate all hold.
The certificate supplies an endpoint with at least 256 accepted candidates and
strict accepted-count progress for every still-incomplete full-block prefix
from block four before that endpoint. It is a deterministic condition on one
exact SHAKE128 stream, not a distribution axiom or a theorem that every input
has a certificate.

For the eta path, the proofs establish that:

- `__poly_sample_mod3`, `__poly_sample_mod3_leq26`, and
  `__poly_sample_mod3_leq8` compute the centered residue in
  `{0, 1, -1}` under their actual input bounds `242`, `26`, and `8`;
- the finite 2048-word-destination consumer returns a counter between its
  incoming value and 256;
- assuming an incoming centered prefix, every output word through the returned
  counter has signed value in `[-1, 1]`;
- its writes are confined to the 256-word polynomial region beginning at
  `base`; and
- given an exact 136-byte block, `eta_consume2048_block136` returns an
  array/counter pair whose stored signed prefix and counter correspond to
  `take 256 (incoming ++ decoded_block)`, where bytes below 243 contribute five
  centered base-three digits and rejected bytes contribute no values. This cap
  includes the case where only a prefix of an accepted byte's five digits fits.

`eta_consume2048_ll` proves unconditional termination of this generated finite
consumer with a variant over the remaining bytes and its `live` transition.
It does not claim that one block fills the polynomial or that the whole eta
leaf terminates.

The centered-range, frame, and exact finite-stream invariants are lifted through
the whole eta leaf and the actual generated eta vector caller. Under Hoare
partial correctness, the leaf returns a complete centered 256-coefficient
polynomial and preserves every word outside its destination block. For any
nonnegative vector count whose `count * 256` words fit in `BArray8192`—
necessarily `0..8`—the caller returns a centered vector, preserves every word
outside the selected vector block, and gives every selected slot its own exact
finite SHAKE256 decoded-prefix witness.

Under its 64-byte seed-slice and destination-capacity bounds, the conditional
`eta2048_leaf_stream` theorem additionally follows the real eta leaf from the
exact padded SHAKE256 seed/nonce state through every successive 136-byte
squeeze at offset zero. On termination, its exact capped decoder result has
size 256 and equals the stored signed prefix. `expand_eta_stream` lifts this
finite result through the actual generated eta vector caller, and
`expand_eta_stream_correct` combines it with the centered-range and
outside-vector frame contracts.

`eta2048_leaf_progress_ll` separately proves probability-one termination of
that actual generated leaf when the initial seed, seed offset, nonce, base,
destination capacity, 64-byte slice bound, and an explicit finite
`eta_progress_prefix` certificate all hold. The certificate includes a finite
full endpoint and strict decoded-prefix progress for every still-incomplete
block before it. It is a deterministic condition on one exact SHAKE256 stream,
not a distribution axiom or a theorem that every input has a certificate.

For the specialized SHAKE128 and SHAKE256 initializers, the proofs establish
exact target-functional framing: each procedure starts from a zeroed 200-byte
state, absorbs respectively 32 or 64 bytes from the requested seed slice,
absorbs the low two nonce bytes in little-endian order, and XORs the domain
separator and final rate bit into the target lanes. The byte/lane bridge then
identifies those raw states with exact one-block `seed || nonce_le16` padding
states. SHAKE256 uses the pinned `HAETAE_FIPS202` definition; SHAKE128 is the
analogous short-message specialization over pinned `HAETAE_Keccak1600`.

For the squeeze procedures, the proofs establish that the state returned by
the internal permutation call is exactly the abstract 24-round
`keccak_f1600_lanes` transition from its input state. They then establish exact
little-endian serialization of that returned state: 168 bytes for SHAKE128 and
136 bytes for SHAKE256. Every output-buffer byte outside the selected block is
preserved. These one-call lane-level contracts are composed with the
initializers through the checked byte/lane bridge by strong Hoare theorems:
the returned state equals the official-model post-permutation byte state, the
output block equals its first rate prefix, and the outside-buffer frame is
preserved.

The proof-only `CheckedShakeBlocks` wrappers extend that composition to every
nonnegative block count whose total output interval fits in `BArray1024`. Each
wrapper calls one actual extracted initializer and then its actual extracted
squeeze procedure at consecutive rate-sized offsets. The final state is the
corresponding number of Keccak byte iterations from the exact padded
`seed || nonce_le16` state; each retained block is the rate prefix after its
permutation; and every byte outside the total interval is unchanged. This is a
bounded retained-output result, not an arbitrary/full SHAKE stream. Separately,
the uniform-leaf proofs follow the real overwrite control flow: the reachable
even buffer lengths force every later offset to zero, each actual squeeze is
the next abstract SHAKE128 block, and the following consumer extends the exact
accepted prefix. The eta-leaf proof follows its offset-zero overwrite loop in
the same finite-state style, but with 136-byte SHAKE256 blocks and its exact
centered-trit decoder. These leaf-specific results are still finite Hoare
partial correctness, not arbitrary infinite-stream or termination theorems.

The fixed-bound infrastructure has separate unconditional losslessness
lemmas: `shake128_init_seedbuf_ll`, `shake256_init_seedbuf_ll`,
`squeeze128_ll`, and `squeeze256_ll`, supported by the corresponding Keccak-f
losslessness stack. These facts concern bounded initializer/permutation/output
loops and do not establish rejection-loop termination.

The target-functional results are proved directly about procedures in the
generated `KeygenSamplerCallersTarget` theory. The proof-only composition
modules call those actual generated procedures rather than substitute an
abstract implementation. No axiom declaration or admitted/aborted proof
appears in these authored files.

## Checked artifacts

| Role | Artifact |
| --- | --- |
| Generated target | `easycrypt/extract/keygen-sampler-callers/KeygenSamplerCallersTarget.ec` |
| Uniform consumer specification | `easycrypt/spec/KeygenUniformXofLeafSpec.ec` |
| Uniform consumer refinement | `easycrypt/refinement/TargetKeygenUniformXofLeaf.ec` |
| Eta consumer specification | `easycrypt/spec/KeygenEtaSamplerSpec.ec` |
| Eta consumer refinement | `easycrypt/refinement/TargetKeygenEtaSampler.ec` |
| Uniform caller and eta-vector finite-stream predicates and composition lemmas | `easycrypt/spec/KeygenSamplerCallersSpec.ec` |
| Uniform/eta caller and proof-only paired-attempt refinement | `easycrypt/refinement/TargetKeygenSamplerCallers.ec` |
| Keccak 200-byte-state/lane adapter | `easycrypt/spec/KeygenKeccak1600Spec.ec` |
| Generated 24-round Keccak-f refinement | `easycrypt/refinement/TargetKeygenKeccak1600.ec` |
| SHAKE128/SHAKE256 framing and serialization specification | `easycrypt/spec/KeygenShakeStreamSpec.ec` |
| SHAKE128/SHAKE256 framing and squeeze refinement | `easycrypt/refinement/TargetKeygenShakeStream.ec` |
| Seed-only SHAKE256 expansion specification | `easycrypt/spec/KeygenSeedXofSpec.ec` |
| Extracted seed-expansion Hoare refinement | `easycrypt/refinement/TargetKeygenSeedXof.ec` |
| Compilation order | `manifests/keygen-sampler-callers-proof-files.txt` |
| Verification command | `scripts/verify-keygen-sampler-callers-proof.sh` |
| Retained summary | `logs/keygen-sampler-callers-proof-summary.txt` |

The uniform, eta, Keccak, SHAKE-stream, and seed-XOF
specification/refinement pairs extend the existing caller-schedule gate. They
are authored proof files, not additional Jasmin extraction surfaces. The
unified generated target selects the three caller roots plus
`_kp_expand_seedbuf` and has an exact 25-file, 31-procedure closure.

## Uniform-consumer theorems

`KeygenUniformXofLeafSpec` defines byte-level frame predicates for the two
destination array sizes and accepted-prefix predicates over 32-bit words. For
the first-buffer result, `uniform_le16` decodes two consecutive bytes in
little-endian order, `uniform_candidates` enumerates a pair prefix, and
`uniform_accepted` filters it with the strict `< uniform_q_i` guard.
`decoded_prefix8192` and `decoded_prefix32768` state that the stored word prefix
equals that accepted list in order. The no-wrap and single-store lemmas connect
the extracted `W64` base/counter address calculation to these predicates.

`TargetKeygenUniformXofLeaf` proves:

| Generated consumer | Frame theorem | Accepted-prefix theorem | Exact first-672-byte theorem | Exact 168-byte continuation theorem |
| --- | --- | --- | --- | --- |
| `__kp_poly_uniform_consume_2048` | `consume2048_frame` | `consume2048_range` | `consume2048_first672` | `consume2048_block168` |
| `__poly_uniform_consume` | `consume8192_frame` | `consume8192_range` | `consume8192_first672` | `consume8192_block168` |

The range theorems follow the actual acceptance guard `t < 64513`: rejected
16-bit candidates do not extend the prefix, while accepted candidates are
stored at `base + ctr` and extend it by one word. A zero incoming counter can
use the specification's empty-prefix lemma.

The two `first672` theorems follow the concrete byte loads, zero extensions,
eight-bit shift, and OR used to assemble each candidate. Their existential
processed-pair postcondition is exact for the accepted output prefix. It does
not assert that all 336 pairs were examined when the output reaches 256, and it
does not state a closed `take 256 (uniform_accepted bytes 336)` formula.

The two `block168` theorems use the same concrete decoder with an incoming
accepted list. On termination, `0..84` processed pairs extend that list exactly,
and the full-or-exhausted alternative prevents an unfinished non-full block.
`uniform_candidates_cat_even` and `uniform_accepted_cat_even` join the preceding
even-length byte prefix to each new block without changing candidate order.

The same refinement file lifts the consumer invariants through the complete
leaf loops:

| Generated whole leaf | Frame theorem | Full-range theorem | Finite stream/decoded-prefix theorem | Conditional totality theorem |
| --- | --- | --- | --- | --- |
| `_kp_poly_uniform_at_seedbuf_2048` | `uniform2048_leaf_frame` | `uniform2048_leaf_range` | `uniform2048_leaf_stream` | `uniform2048_leaf_progress_ll` |
| `_kp_poly_uniform_at_seedbuf_8192` | `uniform8192_leaf_frame` | `uniform8192_leaf_range` | `uniform8192_leaf_stream` | `uniform8192_leaf_progress_ll` |

On termination, each range theorem uses the loop-exit condition to establish
that the returned array has a bounded prefix of exactly 256 coefficients. The
frame theorems cover the same whole procedures. Since these are ordinary Hoare
claims, they do not prove that rejection sampling terminates.

## Uniform-leaf stream and decoder composition

Both `uniform2048_leaf_stream` and `uniform8192_leaf_stream` contain an exact
`seq 17` cut after the initializer and four initial squeeze calls, immediately
before the first consumer. Under
`W64.to_uint seedoff + 32 <= BArray128.size`, each cut proves:

- `sp_0` is the fourth `squeeze_state_iter` state from the exact padded
  `seed || nonce_le16` input;
- `bufp` has four matching 168-byte blocks at offsets `0`, `168`, `336`, and
  `504`;
- the retained region is the flat 672-byte `shake128_squeeze_bytes` FIPS
  prefix;
- `bufp` equals the original `buf` outside `[0, 672)`; and
- the concrete locals are `off = 504`, `ctr = 0`, and `buflen = 672`.

The prelude cuts call `shake128_init_seedbuf_padded_state` for the exact
initialized state, apply the checked squeeze contract four times, and derive
the flat prefix from `shake128_squeeze_blocks_fips`. Each stream proof then uses
a separate `seq 1` cut across the first actual consumer. Under the same
seed-slice capacity hypothesis, it instantiates the matching `first672` theorem
with
`shake128_squeeze_bytes (shake128_seed_nonce_padded_state ...) 4` and records:

- an existential processed count from 0 through 336 candidate pairs;
- counter equal to accepted-list size, with that size at most 256;
- the exact accepted values stored in order as a decoded and bounded prefix;
- preservation outside the reserved 256-word polynomial; and
- the terminal alternative `ctr = 256` or all 336 pairs processed.

The enclosing-loop invariant then carries the exact abstract state, number of
squeezed blocks, number of processed pairs, decoded accepted prefix, bound, and
frame. Its reachable buffer length is 672 at the first loop entry and 168 after
each later squeeze. Both values are even, so the generated
`off = buflen & 1` is exactly zero. Consequently the generic carry-copy loop has
zero iterations, the actual squeeze overwrites offset zero with the next exact
168-byte block, and its returned state is the next `squeeze_state_iter` state.
When the output is not yet full, the preceding consumer's full-or-exhausted
postcondition says that all available pairs were processed. The matching
`block168` theorem and the even-concatenation lemmas therefore extend the one
global accepted list with the accepted values from `0..84` candidates in the
new block, without a gap or reordering.

At loop exit, `ctr = 256`. The exported conditional postcondition discards the
procedure locals but retains witnesses `blocks >= 4` and
`0 <= pairs <= 84 * blocks`, size 256 for the accepted prefix of the exact
finite SHAKE128 byte sequence, and equality between that list and the stored
decoded prefix. Local state, `off`, `ctr`, and `buflen` snapshots are not
available in a procedure postcondition; the destination frame remains a
separate whole-leaf theorem. All claims in this section are ordinary Hoare
partial correctness and do not by themselves prove leaf termination or
losslessness. They also do not establish distributional uniformity or
arbitrary infinite-stream correctness.

The separate pHoare proofs use the rank `256 - ctr` together with
`uniform_progress_prefix`. While the output is incomplete, the certificate
keeps the current full-block count below its finite limit and forces the next
exact block to increase the accepted-prefix count. Thus each actual whole leaf
terminates with probability one under that explicit condition. This proves
neither a certificate for every concrete input nor caller termination or
almost-sure termination under a random-input model. The separate parent-module
prefix proof lifts explicit per-call certificates through only the exact
mode-2 callers and first attempt.

## Uniform matrix and vector callers

`KeygenSamplerCallersSpec.caller_uniform_values` fixes the uniform caller seed
offset to zero and applies `uniform_accepted` to the exact finite SHAKE128 byte
sequence for a given nonce, `blocks`, and processed-pair count. The caller
predicates retain per-polynomial `blocks >= 4` and
`0 <= pairs <= 84 * blocks` witnesses for every destination polynomial:

- `uniform_vector_stream8192` uses base `slot * 256` and nonce
  `256 * k + m + slot`; and
- `uniform_matrix_stream32768` uses base
  `(row * cols + col) * 256` and nonce `256 * row + col`.

Every witness list has size 256 and equals the corresponding stored decoded
prefix. `uniform_vector_range8192` and `uniform_matrix_range32768` state that
all selected coefficients are below 64513. `uniform_vector_frame8192` and
`uniform_matrix_frame32768` preserve every byte outside respectively the first
`k * 256` and `rows * cols * 256` words.

`TargetKeygenSamplerCallers` proves the combined contracts directly for the
actual generated procedures:

| Generated caller | Combined stream/range/frame theorem | Capacity bound |
| --- | --- | --- |
| `_kp_polyveck_expand_vecA` | `expand_vecA_stream_correct` | `0 <= k <= 8` |
| `_kp_polymatkm_expand_matA` | `expand_matA_stream_correct` | `rows * cols <= 32` |

The vector proof extends a linear prefix. The matrix proof tracks
lexicographically visited row/column cells and rolls the completed inner loop
into the next row. Byte-to-word frame lemmas preserve every earlier decoded
prefix across later disjoint leaf writes. These are exact finite Hoare
partial-correctness theorems; they do not prove termination or independence.

The raw uniform SHAKE128 inputs are also characterized exactly.
`caller_uniform_seed_input_prefix` proves that positions `0..31` equal the
corresponding bytes of the same raw `BArray128` at offset zero.
`mode2_matrix_uniform_nonce_input_tail` proves positions 32 and 33 are
`[col, row]`; `mode2_vector_uniform_nonce_input_tail` proves they are
`[3 + slot, 2]`.

## Proof-only mode-2 uniform pair

`CheckedMode2UniformPair.expand` invokes the actual generated matrix and vector
uniform callers with dimensions `(2, 3)` and passes the same raw `BArray128` to
both. `checked_mode2_uniform_pair_correct` composes their exact stream, range,
and aggregate byte-frame postconditions.

This wrapper is not the extracted `_keypair_full_m23`. Its theorem does not
identify the raw prefix as rho/`seedA`, connect the array to
`_kp_expand_seedbuf`, prove actual parent dataflow, or establish termination or
a distribution. The separate proof-only parent-module prefix connects the
exact expanded array to both uniform callers and proves probability-one
termination under six matrix and two vector endpoint certificates. It still
does not prove the actual parent or a distribution.

## Eta-consumer theorems

`KeygenEtaSamplerSpec.centered_trit` maps an unsigned word to its residue
modulo three, representing residue two as `W32.of_int (-1)`. The theory proves
that its signed interpretation is between `-1` and `1` and records the exact
fixed-point identity used by the generated division-by-three steps. Its exact
list model uses:

- `eta_decode_byte`, which maps a byte satisfying `0 <= byte < 243` to five
  centered base-three digits in low-to-high order and maps every other integer
  to `[]`;
- `eta_decode_bytes`, which flattens those lists without reordering; and
- `eta_fill values bytes = take 256 (values ++ eta_decode_bytes bytes)`, which
  models the concrete output cap, including truncation after any of the five
  stores for one accepted byte.

`eta_decoded_prefix8192` compares the signed interpretation of each stored
`W32` word with that exact integer list. The concatenation, sequential-fill,
single-store, and frame lemmas allow the consumer and leaf proofs to preserve
this relation block by block.

`TargetKeygenEtaSampler` proves:

- `mod3_full_correct` for inputs at most 242;
- `mod3_leq26_correct` for inputs at most 26;
- `mod3_leq8_correct` for inputs at most 8;
- `eta_consume2048_block136`, which applies the exact decoder and 256-value cap
  to one 136-byte block from an incoming exact decoded prefix;
- `eta_consume2048_counter`, which bounds the returned counter; and
- `eta_consume2048_centered`, which preserves an incoming centered interval
  and extends it through the returned counter; and
- `eta_consume2048_frame`, which preserves every word outside the complete
  destination polynomial region.

The exact block theorem follows all five generated conditional stores. Bytes
at least 243 are rejected before any store. For an accepted byte, the concrete
division-by-three steps expose the five low-to-high digits; if the counter
reaches 256 between those steps, `eta_fill` retains exactly the digits written
before the guard became false. Together, the theorems give exact finite-block,
counter, centered-interval, and frame partial-correctness properties.

The same refinement file proves the whole-leaf contracts:

| Generated whole eta leaf | Centered-range theorem | Frame theorem | Combined theorem | Finite stream theorem | Conditional totality theorem |
| --- | --- | --- | --- | --- | --- |
| `_kp_poly_uniform_eta_at_seedbuf_2048` | `eta2048_leaf_centered` | `eta2048_leaf_frame` | `eta2048_leaf_correct` | `eta2048_leaf_stream` | `eta2048_leaf_progress_ll` |

On termination, the loop-exit condition raises the consumer prefix to exactly
256 centered coefficients. The frame theorem preserves every 32-bit word
outside the leaf's 256-word destination block. These range/frame facts are
separate from the exact finite-stream theorem.

## Eta-leaf stream and decoder composition

Under `W64.to_uint seedoff + 64 <= BArray128.size` and
`base_i + eta_poly_words_i <= BArray8192.size %/ 4`, the eta stream proof
starts from `shake256_init_seedbuf_padded_state`, the exact pinned SHAKE256
padded state for the selected seed slice and low two nonce bytes. The generated
leaf keeps `off = 0` and `buflen = 136`. Its initial squeeze and every later
loop squeeze therefore overwrite the same buffer region with the next exact
`shake256_squeeze_block`, while the 200-byte abstract state advances by one
Keccak-f[1600] iteration.

After each squeeze, `eta_consume2048_block136` relates the concrete byte loads,
strict `< 243` guard, modulo-three helpers, and up to five guarded stores to
`eta_fill`. Although the concrete buffer is overwritten, the loop invariant
accumulates the corresponding finite abstract `shake256_squeeze_bytes` sequence
and composes sequential fills. This preserves byte order, rejection decisions,
digit order, and the exact 256-value cap across block boundaries.

At loop exit, the capped decoded list has size 256. The conditional
`eta2048_leaf_stream` postcondition states that this list equals the returned
array's signed decoded prefix. The destination frame remains available from
the separate whole-leaf frame theorem. This is ordinary Hoare partial
correctness: it does not prove that enough accepted bytes exist, that the leaf
terminates without a certificate, or a centered-trit distribution. The
separate proof-only parent-module prefix connects the proved
`_kp_expand_seedbuf` eta slice to all five first-attempt slots; later retries
and the actual full-parent control remain open.

The separate pHoare theorem uses the rank `256 - ctr` together with
`eta_progress_prefix`: while the output is incomplete, the certificate keeps
the current block count below its finite limit and forces the next exact block
to increase the decoded-prefix count. Thus the actual whole leaf terminates
with probability one under that explicit condition. This proves neither a
certificate for every concrete input nor almost-sure termination under a
random-input model.

## Eta vector caller

`TargetKeygenSamplerCallers.expand_eta_correct` composes
`eta2048_leaf_correct` across the actual generated `_kp_polyvec_expand_eta`.
Its nonnegative count and capacity preconditions imply `0 <= count <= 8`. On
termination, `eta_vector_centered8192` covers all `count * 256` selected
coefficients, and `eta_vector_frame8192` preserves every word outside that
vector block.

`caller_eta_values seed start slot blocks` is the exact capped eta decoding of
`blocks` SHAKE256 squeezes from the caller's seed array at fixed offset 32 and
word nonce `start + slot`. `eta_vector_stream8192` requires every selected slot
to have its own `blocks >= 1` witness, a 256-value `caller_eta_values` list, and
an equal signed prefix at base `slot * 256`. `expand_eta_stream` proves this
predicate for the actual generated caller. `expand_eta_stream_correct` combines
it with centered range and the outside-vector frame.

The vector extension theorem uses the current leaf's `poly_frame8192` result to
preserve every previously established decoded prefix. These remain
generated-array partial-correctness results. They do not prove source-pointer safety,
termination, the upstream meaning of the seed array, or a distribution.

## Proof-only mode-2 eta pair

`CheckedMode2EtaPair.expand` is an authored proof-only wrapper. It invokes the
actual generated eta vector caller with count three at `start`, then with count
two at `start + 3`, passing the same input seed array to both calls and returning
the nonce word advanced by five. `checked_mode2_eta_pair_correct` proves exact
stream, centered-range, and frame postconditions for both results.

This wrapper is not the extracted `_keypair_full_m23`. Its theorem does not
connect the seed array to `_kp_expand_seedbuf`, prove the actual retry loop,
establish singular-value rejection, or cover the later `egen - b0` adjustment.
The separate proof-only parent-module prefix connects the exact expanded seed
to this nonce-zero/count-three and nonce-three/count-two first attempt, but
likewise stops before the actual retry/downstream path.

## SHAKE128 and SHAKE256 initializer framing

`KeygenShakeStreamSpec` gives an exact functional description of the bytewise
state updates made before the first permutation. `TargetKeygenShakeStream`
proves:

- `keccak_init_state_zero`, for the target state-zeroing procedure; and
- `shake128_init_seedbuf_framing`, for
  `__kp_shake128_init_seedbuf` with a 32-byte in-bounds seed slice; and
- `shake128_init_seedbuf_padded_state`, which exports the exact padded raw-byte
  initializer state used by the uniform-leaf cuts; and
- `shake256_init_seedbuf_framing`, for
  `__kp_shake256_init_seedbuf` with a 64-byte in-bounds seed slice; and
- `shake256_init_seedbuf_padded_state`, which exports the exact pinned SHAKE256
  padded raw-byte initializer state used by the eta-leaf cut.

The framing theorems follow the target's 32 or 64 seed-byte writes, the two
truncate-and-shift nonce steps (little-endian encoding), the `0x1f` domain
byte, and the variant-specific final rate bit. They are intentionally
target-functional framing theorems. `state_of_barray_state_bytes_le` proves
the raw-byte/official-lane adapter, while `shake128_framing_fips_state` and
`shake256_framing_fips_state` prove equality with the exact specialized padded
states.

## SHAKE128 and SHAKE256 squeeze composition

The same refinement theory proves:

| Generated squeeze procedure | Rate bytes | Serialization/frame theorem |
| --- | ---: | --- |
| `__poly_sample_squeeze128` | 168 | `squeeze128_rate_block` |
| `__poly_sample_squeeze256` | 136 | `squeeze256_rate_block` |

Given an in-bounds output offset and an input 200-byte permutation state, each
theorem states that the returned state is exactly the 24-round lane-level
`keccak_f1600_lanes` transition from that input, that the output block is its
little-endian lane serialization, and that all output-buffer bytes outside the
block equal their input values. These are exact one-call contracts. They do
not by themselves compose successive blocks into an iterative/full stream.

The proof module `CheckedShakeOneBlock` calls each actual extracted initializer
and then its actual squeeze procedure. `shake128_seedbuf_one_block` and
`shake256_seedbuf_one_block` prove respectively that the returned state is the
exact post-permutation byte state, the output contains the exact 168-byte or
136-byte first rate prefix, and every output byte outside the block is
unchanged.

The proof module `CheckedShakeBlocks` takes an integer `nblocks`. Under
`0 <= nblocks`, the 32-byte or 64-byte seed-slice bound, and
`W64.to_uint outoff + nblocks * rate <= BArray1024.size`, it calls the same
actual initializer once and the same actual squeeze procedure `nblocks` times.
`shake128_seedbuf_blocks` and `shake256_seedbuf_blocks` prove three joint
postconditions:

- the final raw byte state is `nblocks` Keccak-f[1600] byte iterations from the
  exact padded seed-and-nonce state;
- block `b` at `W64.to_uint outoff + b * rate` is the rate prefix of iteration
  `b + 1` for every `0 <= b < nblocks`; and
- all output bytes outside `[W64.to_uint outoff, W64.to_uint outoff + nblocks *
  rate)` equal their input values.

The zero-block case returns the initialized padded state and preserves the
entire output array. `shake128_seedbuf_blocks_one_block` and
`shake256_seedbuf_blocks_one_block` explicitly specialize `nblocks = 1` back
to the retained canonical state, FIPS-prefix, and one-block frame contracts.
The specification records the generic properties as `squeeze_state_iter`,
`squeeze_blocks_matches`, and `squeeze_region_frame`; its induction lemmas are
shared by both rates.

`shake128_seedbuf_four_blocks` is the proof-only checked-wrapper corollary for
`nblocks = 4` and output offset zero. It exposes the exact fourth state, the
four retained blocks, the flat 672-byte prefix, and the total-region frame.
The actual-leaf results above are separate in-proof cuts over the real leaf
control flow, not applications of an exported local-snapshot theorem.

The separate seed-only expansion theorem follows the extracted
`_kp_expand_seedbuf` absorb, SHAKE256 finalization, permutation, and 128-byte
output loop. `kp_expand_seedbuf_correct` proves on return that each output byte
equals the corresponding byte among the first 128 SHAKE256 bytes of the
32-byte seed. Its uniform, eta, and key corollaries cover ranges `0..31`,
`32..95`, and `96..127`. This result does not identify the actual parent's
subsequent sampler arguments by itself. The separate
`CheckedMode2ParentSamplerPrefix.run` observer connects the exact result to
actual parent-module sampler procedures for the mode-2 first attempt, but it is
not `_keypair_full_m23` and stops before `_kp_m23_matrix`.

## Reproduction

From `haetae-ref-easycrypt/`, run:

```sh
./scripts/verify-keygen-sampler-callers-proof.sh
```

The gate checks the 64 pinned inputs, rejects extraction drift, compiles the
generated target, six authored specifications, and six authored refinements
in manifest order with
`easycrypt compile -no-eco`, and scans every authored proof file for
`admit`/`abort` and axiom declarations. The retained 2026-07-22 full run ends
with:

```text
RESULT: PASS compiled=13 total=13 mode=-no-eco
```

The retained summary checks 64 pinned inputs, zero extraction drift across 25
files and 31 procedures, all 13 manifest entries with `-no-eco`, no
`admit`/`abort` proof commands, and no axiom declarations. The
uniform caller layer additionally carries those finite decoded prefixes through
both actual generated callers, proves aggregate ranges and byte frames, exposes
the exact mode-2 raw input prefix and nonce tails, and composes the uniform pair
in an authored proof-only wrapper. The eta layer adds the exact 136-byte
consumer contract, conditional offset-zero SHAKE256 stream/decoded-prefix
postcondition for the generated 2048-word leaf, exact per-slot lifting through
the actual generated eta vector caller, and the authored proof-only paired
mode-2 attempt.
The eta layer also includes unconditional finite-consumer losslessness and
`eta2048_leaf_progress_ll`, the certificate-conditioned probability-one
termination theorem for the actual eta whole leaf. The uniform layer likewise
includes `uniform2048_leaf_progress_ll` and `uniform8192_leaf_progress_ll` for
the two actual uniform whole leaves under `uniform_progress_prefix`.

## Explicit exclusions

This result does not prove:

- an arbitrary infinite SHAKE stream theorem; the exported uniform and eta
  leaf results concern exact finite prefixes witnessed on terminating
  executions;
- actual `_keypair_full_m23` sampler composition; both uniform callers, the eta
  vector caller, and authored proof-only pairs are checked separately;
- universal progress-certificate existence, unconditional whole-leaf or caller
  losslessness, or almost-sure termination under a random-input model; bounded
  consumers terminate unconditionally and all three actual leaf variants
  terminate with probability one under their respective explicit deterministic
  certificates, while the exact mode-2 caller and proof-only prefix totality
  theorems require the bundled per-call endpoints;
- uniformity, independence, centered-trit distribution, or any other
  probabilistic property;
- source-pointer separation, source-language memory safety, or an aliasing
  model beyond the generated functional arrays; or
- actual `_keypair_full_m23` retry/downstream composition, singular-value
  rejection, or the later `egen - b0` adjustment. The proof-only
  parent-module prefix closes the on-return `_kp_expand_seedbuf`
  slice-to-caller cut only within that observer.

Both actual uniform leaves link their initial 672 bytes and every later
168-byte squeeze block to one exact finite SHAKE128 sequence. The eta leaf links
every offset-zero 136-byte overwrite block to one exact finite SHAKE256
sequence, applies the exact five-trit rejection decoder with its 256-value cap,
and is now lifted through the actual eta vector caller. The uniform callers
likewise retain each leaf's separate finite witness, range, and aggregate
frame. The two proof-only pairs compose their respective actual caller
invocations over shared raw arrays. The seed-XOF theorem fixes the standalone
128-byte expansion and slices on return. The later proof-only parent-module
prefix connects that result to both uniform callers and the first eta pair and
terminates with probability one under its exact certificate bundle.
Source-pointer safety, distributions, and a semantic theorem for the actual
`_keypair_full_m23` retry/downstream path remain open.
