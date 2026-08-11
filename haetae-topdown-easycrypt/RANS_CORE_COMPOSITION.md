# Mode-2 actual rANS core composition

## Scope

This document records the Week 13 closure of `OBL-RANS-CORE-INVERSE`. The
result is a direct composition theorem over three actual extracted procedures:

```text
RansEncodeTarget.M._rans_encode
  -> HbzFullEncodeTarget.M.__copy_encoded_suffix
  -> RansDecodeTarget.M._rans_decode
```

The sequential caller is the proof-authored `Mode2RansActualHarness.run`.
This is not the production `_encode_hb_z1_full`/`_decode_hb_z1_full` wrapper
theorem.

## Top-level theorem

`Mode2RansCoreActualInverse.actual_rans_encode_copy_decode_inverse` has the
following complete semantic precondition:

```text
arg = (enc_initial, copied_initial, decoded_initial,
       encoder_state_initial, decoder_state_initial, expected_symbols)
and mode2_hbz_symbol_stream expected_symbols
```

It does not assume encoder success, decoder reachability, decoder success,
copied trace equality, decoded equality, or termination.

Its postcondition is a disjunction.

### Actual encoder failure

```text
encoder_bad != 0
decoder_ran = false
decoder_off = 0
decoder_bad = 1
decoded_result = decoded_initial
decoder_state_result = decoder_state_initial
```

The actual copy and decoder calls are skipped by the harness branch.

### Actual encoder success

```text
encoder_bad = 0
decoder_ran = true
decoder_count_input = 1024
decoder_size_input = encoded_size
decoder_alphabet_input = 13
decoder_bad = 0
decoder_off = encoded_size
decoded[0..1024) = expected_symbols[0..1024)
decoded[1024..2048) = decoded_initial[1024..2048)
actual_core_success_result
```

The postcondition also retains the actual encoder suffix relation and the
initial-prefix frame.

## Adapter chain

### Encoder segment to copied trace

The actual encoder theorem returns:

```text
segment_matches encoded off trace
off + size(trace) = 1024
```

The actual copy theorem returns:

```text
slice_eq encoded copied off (size trace)
```

`copied_suffix_is_exact_trace` proves their pointwise composition:

```text
segment_matches copied 0 trace
```

No decoder buffer is chosen as an existential witness.

### Global trace to pointwise decoder reads

Week 12 expresses the nested normalization-loop read contract per symbol and
per byte. `trace_bytes_trace_segment_nth` relates the decoder cursor plus the
local segment offset to the corresponding global `trace_bytes` index.
`segment_matches_implies_exact_decoder_segment_input` then derives every
pointwise read from the copied global segment. The W64-facing corollary
`segment_matches_implies_decoder_word_reads` is the exact form used by the
decoder input constructor.

### Decoder-state construction

`configured_decoder_state` is exactly the result of the harness's three
`BArray24.set64` operations. `configured_decoder_state_fields` proves:

```text
state[0] = W64.of_int 1024
state[1] = W64.of_int encoded_size
state[2] = W64.of_int 13
```

`actual_decoder_input_from_configured_trace` combines these fields, the copied
segment, the size bounds, and the canonical symbol stream into Week 12's
`actual_mode2_decoder_trace_input`.

## W64/int size correspondence

The actual harness computes:

```text
encoded_size = W64.of_int 1024 - encoder_off
```

`encoder_success_size_word_bridge` uses the actual encoder postcondition:

```text
0 <= uint(encoder_off) <= 1020
uint(encoder_off) + trace_size = 1024
```

to derive:

```text
uint(encoded_size) = trace_size
encoded_size = W64.of_int trace_size
4 <= trace_size <= 1024
uint(encoder_off) + uint(encoded_size) = 1024
encoder_off = W64.of_int(uint(encoder_off))
```

The unsigned-order proof is explicit; modular subtraction is not silently
identified with integer subtraction.

## Proof decomposition

The final Hoare proof uses the already compiled top-level theorems in actual
execution order:

1. `actual_rans_encode_trace_refinement`;
2. `copy_encoded_suffix_correct` on the success branch;
3. `actual_rans_decode_trace_refinement` after constructing its input
   predicate from the actual copied post-state.

The generated encoder and decoder loops are not re-inlined. A monolithic
`inline; sim` approach was rejected because it would duplicate two completed
semantic refinements and obscure the only remaining interface obligation.
Passing copied-trace or decoder-read equality as a top-level premise was also
rejected because it would make the composition circular.

## Non-vacuity and limits

`core_composition_preconditions_satisfiable` supplies a canonical all-zero
symbol-array witness for the sole semantic precondition. This proves that the
harness precondition is consistent. It does not prove that the actual encoder
terminates or reaches its success branch.

The following remain open:

- `OBL-RANS-ACTUAL-SUCCESS-WITNESS`;
- encoder and decoder termination/losslessness;
- production full-HBZ wrapper inverse;
- malformed/canonical-input rejection;
- complete signature codec correctness;
- encoding delta zero, Sign/Verify correctness, and implementation security.

## Decision

`OBL-RANS-CORE-INVERSE` is **PROVED — success-conditioned partial
correctness**. Week 14 should compose the actual full HBZ wrappers with the
already proved prepare/apply inverse and this rANS core theorem. The `h` codec
must remain out of scope until that wrapper boundary closes.
