# Week 8 mode-2 HBZ codec obligations

Date: 2026-08-09

## Pinned actual targets

- focused prepare wrapper: `encode_hb_z1_prepare_jazz`
- focused apply wrapper: `decode_hb_z1_apply_jazz`
- focused encoder wrapper: `encode_hb_z1_mode2_full_jazz`
- focused decoder wrapper: `decode_hb_z1_mode2_full_jazz`
- actual full procedures:
  `_encode_hb_z1_full`, `_decode_hb_z1_full`

## Pinned actual parameters

- `count = 1024`
- `m = 13`
- `offset = 6`
- `scale = 1024`
- initial/final state `8388608`

## Week 8 obligation split

| ID | Status | Exact surface | What is already compiled | Remaining edge |
| --- | --- | --- | --- | --- |
| `OBL-HBZ-PREPARE-CORRECT` | `PROVED` | actual prepare leaf | exact symbol mapping and `bad=0` on canonical inputs | none at the leaf layer |
| `OBL-HBZ-APPLY-CORRECT` | `PROVED` | actual apply leaf | exact coefficient reconstruction | none at the leaf layer |
| `OBL-HBZ-PREPARE-APPLY-INVERSE` | `PROVED` | actual prepare/apply composition | leaf inverse before rANS | no buffer or size claim |
| `OBL-HBZ-LEAF-FRAME` | `PROVED` | actual prepare/apply leaves | symbol and coefficient tail frames | bounded arrays only |
| `OBL-SIG-HBZ-ACTUAL-BOUNDARY` | `PROVED` | actual `_encode_hb_z1_full`, `_decode_hb_z1_full` across both extraction routes | exact focused/full extraction identity | no inverse |
| `OBL-RANS-MODE2-HBZ-TABLE-CERTIFICATE` | `PROVED` | actual mode-2 arrays and generic certificate predicate | generic arithmetic certificate plus concrete actual-array corollary | none at the table layer |
| `OBL-RANS-PURE-STEP-INVERSE` | `PROVED` | pure step instantiated by concrete mode-2 table formulas | quotient/slot inverse and reciprocal fast-step corollary | normalization bytes and loops excluded |
| `OBL-RANS-ENC-NORMALIZE` | `PROVED (actual-loop lift)` | normalization loop nested in actual `_rans_encode` | pure 0/1/2 bounds plus exact generated cursor/byte/tail invariant | partial correctness; no separate loop-termination theorem |
| `OBL-RANS-DEC-NORMALIZE` | `PROVED (actual-loop lift)` | normalization loop nested in actual `_rans_decode` | exact 0/1/2-byte replay, cursor movement and no-consume exit | partial correctness; no separate loop-termination theorem |
| `OBL-RANS-NORMALIZE-BYTE-INVERSE` | `PROVED (pure)` | shared `xs/cuts/bytes` trace | normalization list readback | implementation refinements |
| `OBL-RANS-STATE-BOUND-PRESERVATION` | `PROVED (pure)` | concrete mode-2 formulas | `2^23 <= x < 2^31` preserved | actual word/table-load lift |
| `OBL-RANS-ENCODE-REFINEMENT` | `PROVED` (success-conditioned partial correctness) | actual `rans_encode_jazz` / `_rans_encode` | Week 11 tail-aware actual inner exit, generated word update, outer trace closure, and final-store composition prove exact whole-suffix `trace_bytes(actual symbols)` plus size and prefix frame | actual success reachability/termination; decoder refinement is separate |
| `OBL-RANS-DECODE-REFINEMENT` | `PROVED (exact-trace partial correctness)` | actual `rans_decode_jazz` / `_rans_decode` | `actual_rans_decode_trace_refinement`: exact table/state/trace input implies `bad=0`, exact consumption, 1024-symbol recovery and output-tail frame | termination/losslessness and actual encoder-success reachability are separate |
| `OBL-RANS-SUFFIX-COPY` | `PROVED` | actual `__copy_encoded_suffix` | exact pointwise slice plus unused-tail frame | derive `off/size` bounds from actual encoder success |
| `OBL-RANS-ACTUAL-HARNESS-CONTROL` | `PROVED` | actual `_rans_encode`, `__copy_encoded_suffix`, `_rans_decode` | actual success branch and decoder `count/size/m` initialization | no inverse conclusion |
| `OBL-RANS-CORE-INVERSE` | `PROVED` (success-conditioned partial correctness) | actual `_rans_encode`, `__copy_encoded_suffix`, `_rans_decode` in `Mode2RansActualHarness.run` | `actual_rans_encode_copy_decode_inverse`; bridge from encoder segment through actual copy to decoder pointwise reads; failure branch retained | actual success reachability and encoder/decoder termination remain separate |
| `OBL-RANS-ACTUAL-SUCCESS-WITNESS` | `PROVED (fixed all-6 input, Hoare partial correctness)` | actual encoder on all-6 symbols | `Mode2RansActualSuccessWitness.actual_rans_encode_all_six_success`, `full_rans_encode_all_six_success`, `actual_encode_hb_z1_full_zero_success`, `signature_pack_hbz_zero_success_mode2`, `actual_hbz_full_encode_decode_zero_success_mode2`, `signature_pack_unpack_hbz_zero_success_mode2` | every terminating fixed-input run returns success; termination/losslessness, probability-one, and non-vacuous execution remain unproved because no `phoare` theorem was compiled |
| `OBL-SIG-HBZ-ENCODE-DECODE` | `PROVED (success-conditioned partial correctness)` | actual full HBZ wrapper pair | `signature_pack_unpack_hbz_full_actual_exact`, `signature_pack_unpack_hbz_full_inverse_mode2`, `actual_hbz_full_encode_decode_inverse_mode2` | fixed-input success is now witnessed by `Mode2RansActualSuccessWitness.actual_hbz_full_encode_decode_zero_success_mode2`; the theorem still does not claim termination or unconditional reachability |

## Not proved by Week 8 leaf results

- every canonical HBZ always encodes
- decoder success for arbitrary buffers
- canonical parsing
- full signature codec inverse
- `encoding delta = 0`
- Sign output tail reach

## Next gate

Week 9 remains `CONTINUE-RANS`.  The concrete actual-array table certificate
is closed; the single next gate is the normalization-byte stack relation and
the two actual loop refinements.  The `h` codec remains out of scope until the
actual HBZ core/full composition and witness compile.

## Week 9 decision update

Week 9 closes the byte-stack mathematical layer and the actual suffix-copy
procedure. It also compiles direct control theorems for both generated loops
and a unary harness that invokes the actual encoder, actual copy helper, and
actual decoder. The harness branches on the encoder's returned `bad`; success
is not a premise.

The gating relation is now narrower but still open:

```text
actual encoder output
  -> valid_rans_trace(symbols, xs, cuts, bytes)
  -> actual decoder consumes the same trace
  -> decoded symbols / final state / consumed size
```

Because neither arrow is yet a compiled implementation refinement,
`OBL-RANS-CORE-INVERSE` and the HBZ parent remain `PARTIAL`. The control
harness is not cited as an inverse theorem, and no decoder-success or actual
success witness is assumed.

## Week 10 decision update

Week 10 adds a genuine implementation-level inner-loop transition. The
generated `_rans_encode` proof now preserves an exact byte segment and prefix
frame through actual cursor decrement, `set8`, and shift operations, and its
success return has a compiled `4 <= 1024-off <= 1024` bound. Separately, the
actual-array/list recurrence, concrete reciprocal word step, pure 0/1/2
progress, and four-byte state serialization compile.

The Week 10 parent remained `PARTIAL` because its actual inner invariant was
not tail-aware. Week 11 closes that exact encoder edge; the update below is
the current status.

## Week 11 decision update

`actual_rans_encode_trace_closure` directly opens the generated
`RansEncodeTarget.M._rans_encode`. Its success branch now carries the initial
array, actual input symbol suffix, exact pure state, accumulated normalization
bytes, cursor equation, and prefix frame through both generated loops. The
final four generated stores prepend the serialized state. Consequently
`actual_rans_encode_trace_refinement` proves the returned success suffix is
exactly `trace_bytes(symbol_list_of_array(symbols0))` and that the returned
offset plus this trace length is 1024.

Thus `OBL-RANS-ENCODE-REFINEMENT` is **PROVED as success-conditioned partial
correctness**. It neither proves that `_rans_encode` terminates nor that a
successful branch is reachable for all-6 (or any) concrete input. The actual
success witness stays `PARTIAL`; decoder refinement, core inverse, and the HBZ
parent stay `PARTIAL`. Week 12 is `GO-ENCODER` and is restricted to the actual
decoder trace refinement.

## Week 12 decision update

`actual_rans_decode_trace_refinement` directly opens
`RansDecodeTarget.M._rans_decode`. Under a canonical 1024-symbol array, exact
`trace_bytes`, concrete `(count,size,m)=(1024,encoded_size,13)` state, and the
actual mode-2 decode tables, every terminating execution returns `bad=0`,
publishes `off=encoded_size`, recovers all 1024 symbols, and preserves the
decoded array tail `[1024,2048)`. The actual generated final-state guard is
discharged from the internal loop-exit fact `x=2^23`.

Therefore `OBL-RANS-DECODE-REFINEMENT` is **PROVED as exact-trace partial
correctness**. `OBL-RANS-CORE-INVERSE` remains **PARTIAL** because the actual
unary harness has not yet transported the encoder suffix and copy-helper slice
facts into the decoder's exact pointwise trace premise. Encoder success,
encoder/decoder termination, the full HBZ wrapper, and the actual success
witness remain separate. Week 13 is restricted to this single actual-harness
composition edge.

## Week 13 decision update

`actual_rans_encode_copy_decode_inverse` closes the actual core harness. Its
precondition binds the six initial arrays/states to the harness arguments and
requires only `mode2_hbz_symbol_stream symbols`. It does not assume encoder
success, decoder reachability, decoder success, copied-buffer equality, or
decoded equality.

On actual encoder failure the decoder is not run and the initialized decoded
array/state are preserved. On actual encoder success, the proof derives the
exact W64/int size relation, applies the actual suffix-copy theorem, constructs
the decoder's pointwise trace-read relation from the copied post-state, and
applies the actual decoder theorem. The result is decoder `bad=0`, exact
`off=size`, recovery of 1024 symbols, and the decoded tail frame.

Thus `OBL-RANS-CORE-INVERSE` is **PROVED as success-conditioned partial
correctness**. The result is a direct composition theorem over three actual
extracted procedures, not production full-HBZ wrapper correctness. Encoder
success reachability, both termination claims, and the fixed-input success
branch remain separate proof obligations at this stage. Week 14 is restricted
to the actual full-HBZ wrapper composition; the `h` codec remains out of scope
until Week 16.

## Week 14 decision update

`signature_pack_unpack_hbz_full_actual_exact` is the production exact theorem
that aligns the production SignaturePack/Unpack harness with the focused
full-HBZ harness. Its Hoare corollary
`signature_pack_unpack_hbz_full_inverse_mode2` keeps the exact failure/success
split visible:

- `size = 0`: the decoder is skipped and the initialized buffers are
  preserved;
- `size <> 0`: the decoder runs, `bad = 0`, the decoded prefix and tail frame
  are proved, and a concrete `prepared_symbols` witness supplies the trace
  bytes.

Therefore `OBL-SIG-HBZ-ENCODE-DECODE` is now **PROVED (success-conditioned
partial correctness)**. The fixed all-6 success witness now compiles, so the
closed fixed-input statement is failure exclusion for terminating runs only;
termination, losslessness, and non-vacuous reachability remain open.

## Week 15 decision update

`Mode2RansActualSuccessWitness.actual_rans_encode_all_six_success` is the
fixed all-6 success witness. The derived HBZ lift
`actual_hbz_full_encode_decode_zero_success_mode2` and the production wrapper
corollary `signature_pack_unpack_hbz_zero_success_mode2` carry that witness
through the actual wrapper boundary. `OBL-RANS-ACTUAL-SUCCESS-WITNESS` is now
`PROVED (fixed all-6 input, Hoare partial correctness)`.

## Week 16 decision update

Restrict Week 16 to `OBL-SIG-H-ENCODE-DECODE` only. Do not widen beyond the
`h` codec.
