# Week 12 report — actual rANS decoder semantic refinement

## Decision

**GO-DECODER.**  `OBL-RANS-DECODE-REFINEMENT` is proved as partial
correctness for the actual generated mode-2 decoder.  The encoder/copy/decoder
harness inverse is not yet compiled, so `OBL-RANS-CORE-INVERSE` remains
`PARTIAL` and Week 13 has one composition goal.

## Direct implementation theorem

The fresh-compiled theorem is:

```easycrypt
lemma actual_rans_decode_trace_refinement
    (decoded0 expected_symbols buffer0 : BArray2048.t)
    (state0 : BArray24.t)
    (encoded_size : int) :
  hoare [RansDecodeTarget.M._rans_decode :
    symsp = decoded0 /\
    statep = state0 /\
    bufp = buffer0 /\
    symbolwp = jmode2_hb_z1_symbol_words /\
    dsymswp = jmode2_hb_z1_dsyms_words /\
    actual_mode2_decoder_trace_input
      expected_symbols buffer0 state0 encoded_size
    ==>
    actual_mode2_decoder_trace_post
      decoded0 expected_symbols res encoded_size].
```

The input predicate expands to these exact premises:

1. `mode2_hbz_symbol_stream expected_symbols`;
2. `encoded_size = size(trace_bytes(symbol_list_of_array expected_symbols))`;
3. `4 <= encoded_size <= 1024`;
4. the initial state's size word has unsigned value `encoded_size`;
5. `buffer0[0..encoded_size)` matches that exact `trace_bytes` list;
6. every generated normalization-byte read in a trace segment matches the
   corresponding list byte;
7. state fields are exactly `count=1024`, `size=encoded_size`, `m=13`;
8. actual mode-2 `symbol_words` and `dsyms_words` arrays are passed.

The postcondition expands to:

```text
state_out[1] = 0
state_out[0] = W64.of_int(encoded_size)
forall i, 0 <= i < 1024 -> decoded[i] = expected_symbols[i]
forall i, 1024 <= i < 2048 -> decoded[i] = decoded0[i]
```

The internal final state is not exported by the generated ABI.  The proof
derives `x=2^23` in `decoder_outer_trace_exit_components`, uses it to show the
actual final-state reject is not taken, and publishes only the actual returned
arrays.

## Compiled implementation edges

- Initial four-byte parse equals `fst(encode_trace syms)` and lies in
  `[2^23,2^31)`.
- Concrete `symbol_words` lookup selects the expected symbol.
- Concrete `dsyms_words` fields implement the mathematical decoder word-step.
- The actual inner normalization loop consumes exactly 0, 1, or 2 bytes.
- The actual outer loop extends the decoded prefix by one coefficient and
  preserves the untouched tail each iteration.
- Loop exit gives `i=1024`, `x=2^23`, and `off=encoded_size`.
- Both actual final reject checks pass and the actual state stores publish
  `off` and `bad=0`.

The central theories are:

- `Mode2RansDecoderCursor.ec` — base state/cursor/output-prefix model;
- `Mode2RansDecoderWordStep.ec` — concrete table-lookup mathematical leaves;
- `Mode2RansDecoderNormalization.ec` — replay and 0/1/2-byte normalization;
- `Mode2RansDecoderActualWord.ec` — W32/W64 word arithmetic;
- `Mode2RansDecoderGeneratedStep.ec` — generated table-load expressions;
- `Mode2RansDecoderCursorSteps.ec` — state/cursor boundaries;
- `Mode2RansDecoderActualTrace.ec` — outer/inner semantic invariants;
- `Mode2RansDecoderTopHoare.ec` — direct generated-procedure Hoare theorem.

## Reused results and trust boundary

Week 12 reuses, without modification:

- Week 8 concrete HBZ table certificates;
- Week 9 `encode_trace`, `trace_states`, `trace_segments`, `trace_cuts`, and
  `trace_bytes`;
- Week 9/10 normalization-byte readback and state bounds;
- Week 10 array/list and word-arithmetic bridges;
- Week 11 exact actual encoder trace refinement;
- the actual suffix-copy theorem.

None of these reused results is treated as decoder correctness.  Week 12 opens
the generated `_rans_decode` body and proves its loops directly.  The generated
target hash remains
`2659860ffe3dff9dd5d5bb6fd123a6498cf0ad38784088b0c7ab6e62377a3f75`.
`jasmin2ec`, EasyCrypt, SMT backends, and the pinned generated arrays remain in
the TCB described by `ASSUMPTIONS.md`.

## Failed approaches and adopted decomposition

- Extending the Week 9 control theorem could only retain `bad in {0,1}` and
  could not express symbol recovery.
- A monolithic `inline; sim` attempt was rejected because the outer symbol
  loop and variable-length normalization loop require different invariants.
- A first top-level initialization proof split both generated reject guards
  syntactically and left four brittle WP branches.  The final proof instead
  derives the exact parse bounds and discharges the nested generated guards by
  consequence.
- The final proof does not expose internal `x` through a wrapper.  It projects
  the state/cursor facts at loop exit and proves the actual generated checks.

## Non-vacuity and limitations

The exact-trace premise is non-circular: it contains neither `bad=0` nor
decoded output equality.  It is the mathematical relation already produced by
the Week 11 encoder theorem on its success branch.  The remaining sequential
adapter must still transport the actual copied suffix to the decoder's
pointwise read relation.

The following remain unproved:

- actual encoder success and local rANS losslessness;
- termination of `_rans_encode` or `_rans_decode`;
- the actual encoder→copy→decoder harness inverse;
- the full HBZ wrapper inverse and successful witness;
- canonical malformed-input rejection, full signature parsing, and any
  encoding/security delta.

## Claim status

| Claim | Week 12 status | Meaning |
|---|---|---|
| `OBL-RANS-DECODE-REFINEMENT` | **PROVED** | exact-trace, actual generated decoder, partial correctness |
| `OBL-RANS-CORE-INVERSE` | **PARTIAL** | encoder and decoder refinements plus copy are separate; harness composition remains |
| `OBL-RANS-ACTUAL-SUCCESS-WITNESS` | **PARTIAL** | no EasyCrypt proof that the actual success branch is reached |
| `OBL-SIG-HBZ-ENCODE-DECODE` | **PARTIAL** | full wrapper composition and witness remain |

## Verification

The final verification entry point is:

```sh
./haetae-topdown-easycrypt/scripts/verify-all.sh
```

It fresh-compiles all 65 authored targets with `-no-eco`, including an
individual compile log for `Mode2RansDecoderTopHoare.ec`; regenerates focused
extractions and the concrete table certificate; scans for proof holes, axioms,
debug declarations, manifest drift and claim overreach; runs selected upstream
baselines; checks the read-only source hashes; and builds the LaTeX notes.
The authoritative outputs are `logs/verify-all-summary.txt` and
`logs/compile-Mode2RansDecoderTopHoare.log`.

The start-of-sprint invocation is preserved in
`logs/verify-all-before-week12.log`.  That invocation was interrupted after
the first targets while concurrent proof work was being initialized; the
completed Week 11 baseline remains the historical 57-target evidence.  The
eight Week 12 decoder theories raise the current manifest to 65 targets. The
final clean run is the authoritative Week 12 regression result.

## Week 13 single recommendation

Prove one theorem over `Mode2RansActualHarness.run` that composes:

```text
actual_rans_encode_trace_refinement
  -> copy_encoded_suffix_correct
  -> actual_rans_decode_trace_refinement
```

The only new semantic adapter should convert the copied `slice_eq` result and
the encoder's `segment_matches` result into the decoder's exact pointwise
trace-read premise.  Do not start the `h` codec or full HBZ wrapper until that
actual harness inverse fresh-compiles.
