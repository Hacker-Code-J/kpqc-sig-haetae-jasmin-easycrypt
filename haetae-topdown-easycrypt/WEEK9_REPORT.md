# Week 9 report

Date: 2026-08-08

## Outcome

Week 9 is **CONTINUE-RANS**.

The sprint closed three real edges:

1. the pure `xs/cuts/bytes` byte-stack and W32/W64 normalization semantics;
2. the actual `__copy_encoded_suffix` pointwise copy and tail frame;
3. a unary harness containing the actual generated encoder, copy, and decoder
   calls, including an actual-result-driven failure/success branch and exact
   decoder input-field initialization.

It did not close the two generated outer-loop refinements. Consequently
`OBL-RANS-CORE-INVERSE` and `OBL-SIG-HBZ-ENCODE-DECODE` remain `PARTIAL`.

## Baseline

Before Week 9 edits, `scripts/verify-all.sh` passed all 38 Week 8 authored
targets with `-no-eco`, extraction/certificate regeneration, baselines,
read-only drift checks, and LaTeX. The preserved summary is:

```text
logs/week9-baseline-summary.txt
RESULT PASS authored-targets=38 cache=-no-eco
```

## Fresh-compiled pure trace theorems

`Mode2RansByteStack.ec` defines the shared trace without assuming it at the
actual composition boundary. The principal compiled facts are:

- `renorm_len_le2`: under the mode-2 symbol/state range, normalization length
  is between 0 and 2;
- `renorm_reduced_bounds`: the reduced state is in
  `1 <= xr < hbz_xmax(s)`;
- `renorm_bytes_readback`: decoder-order append of the emitted segment restores
  the pre-normalized state;
- `serialize32_parse_inverse`: the little-endian four-byte state parses back;
- `normalized_fast_step_state_bounds` and `encode_trace_state_bounds`: the
  canonical pure trace preserves `2^23 <= x < 2^31`;
- `trace_head_symbol_selected`, `trace_head_decodes_to_reduced`, and
  `trace_head_normalization_readback`: the trace head is selected and inverted
  by the Week 8 concrete-table step;
- `valid_rans_trace_canonical`: canonical construction of `xs/cuts/bytes`.

These are mathematical or word-semantics lemmas. They contain no generated
encoder/decoder procedure and are not labeled implementation refinement.

`Mode2RansNormalization.ec` compiles the exact W32/W64 facts used by the code:

- `encoder_shift8_uint`
- `encoder_low_byte_uint`
- `decoder_append_word_uint`
- `decoder_append_encoder_byte`
- `encoder_two_byte_decoder_order`
- `cursor_decrement_no_underflow`
- `cursor_two_decrements_no_underflow`

The two-byte order is `[high,low]` in decoder order because the encoder writes
the low byte first while decrementing its cursor.

## Actual suffix-copy theorem

`Mode2RansSuffixCopy.copy_encoded_suffix_correct` directly targets
`HbzFullEncodeTarget.M.__copy_encoded_suffix`:

```text
encp = enc0 /\ outp = out0 /\
off = of_int(off0) /\ size = of_int(n) /\
0 <= off0 /\ 0 <= n /\ off0+n <= 2048
  ==>
slice_eq(enc0, result, off0, n) /\
suffix_frame(out0, result, n)
```

This is Hoare partial correctness. It uses the actual copy loop, not a
constructed decoder buffer. The remaining parent edge is to derive the
integer bounds from actual encoder success.

## Actual encoder and decoder control boundaries

The following theorems directly contain generated procedures and
fresh-compile:

- `actual_rans_encode_mode2_control` on
  `RansEncodeTarget.M._rans_encode`;
- `actual_rans_encode_mode2_jazz_control` on the exported wrapper;
- `actual_rans_decode_mode2_control` on
  `RansDecodeTarget.M._rans_decode`;
- `actual_rans_decode_mode2_jazz_control` on the exported wrapper.

Their exact result is deliberately small: concrete mode-2 tables/count/state
inputs are fixed and the published `bad` is proved to be either zero or one.
They do not prove that array output matches `valid_rans_trace`, that decoded
symbols match, or that final state/consumed size is correct. Thus the filenames
do not promote the theorems to completed refinement claims.

## Actual unary harness and failure branch

`Mode2RansActualHarness.run` directly executes:

```text
RansEncodeTarget.M._rans_encode
  -> if actual encoder_bad = 0
       HbzFullEncodeTarget.M.__copy_encoded_suffix(actual off, actual size)
       decoder state := (1024, actual size, 13)
       RansDecodeTarget.M._rans_decode
```

`actual_rans_harness_branches_on_encoder_result` proves:

```text
encoder_bad in {0,1} /\
(decoder_ran <=> encoder_bad = 0) /\
(decoder_ran =>
  decoder_count_input = 1024 /\
  decoder_size_input = encoded_size /\
  decoder_alphabet_input = 13)
```

Encoder success is not a precondition. The failure branch executes no decoder.
The theorem does not assume or conclude `decoder_bad=0`.

## Exact open implementation refinements

The compiled work leaves two semantic edges:

1. `OBL-RANS-ENCODE-REFINEMENT`: at outer-loop index `i`, connect actual
   `(x,off,encp)` to the pure trace for `symbols[i..1024)`, including final
   state serialization, byte frame, and success bounds;
2. `OBL-RANS-DECODE-REFINEMENT`: from the actual copied trace, maintain decoded
   prefix, `x=xs[i]`, `off=cuts[i]`, and prove the final `x=2^23`,
   `off=size`, `bad=0`, symbol equality, and output frame.

The weak control invariant successfully exposed every nested early/failure
branch, but it cannot derive those relations. Direct encoder/decoder lockstep,
an arbitrary replay buffer, and trace-validity/decoder-success premises were
rejected.

## Non-vacuity

- The pure trace premises have compiled concrete witnesses.
- The actual decoder-state predicate has a compiled witness at size 4.
- The actual harness success branch is not known to have an EasyCrypt witness.
  `OBL-RANS-ACTUAL-SUCCESS-WITNESS` therefore remains `PARTIAL`.
- No execution log is used as a replacement for the missing theorem.

The actual core claim is not promoted merely because its antecedent could be
conditional. No actual decoder-success theorem exists yet.

## Claim status

| Claim | Status | Meaning |
| --- | --- | --- |
| `OBL-RANS-ENC-NORMALIZE` | `PROVED (pure/word leaf)` | 0/1/2 encoder normalization and word semantics |
| `OBL-RANS-DEC-NORMALIZE` | `PROVED (pure/word leaf)` | one/two-byte decoder append inverse |
| `OBL-RANS-NORMALIZE-BYTE-INVERSE` | `PROVED (pure)` | common byte segment readback |
| `OBL-RANS-STATE-BOUND-PRESERVATION` | `PROVED (pure)` | canonical trace state remains in `[2^23,2^31)` |
| `OBL-RANS-SUFFIX-COPY` | `PROVED` | actual copy procedure, explicit bounds |
| `OBL-RANS-ACTUAL-HARNESS-CONTROL` | `PROVED` | three actual calls and actual-result branch; no inverse |
| `OBL-RANS-ENCODE-REFINEMENT` | `PARTIAL` | direct control theorem only; trace postcondition open |
| `OBL-RANS-DECODE-REFINEMENT` | `PARTIAL` | direct control theorem only; trace consumption open |
| `OBL-RANS-CORE-INVERSE` | `PARTIAL` | actual harness exists; inverse conclusion absent |
| `OBL-RANS-ACTUAL-SUCCESS-WITNESS` | `PARTIAL` | no compiled all-6 actual success witness |
| `OBL-SIG-HBZ-ENCODE-DECODE` | `PARTIAL` | actual core/full wrapper/witness remain |

## Verification

The final aggregate verifier checks 44 authored targets, Week 9 theorem
surfaces, proof holes/axioms/debug declarations, manifest completeness,
focused extraction and table-certificate regeneration, source/read-only
drift, selected baselines, and LaTeX. The command is:

```sh
./haetae-topdown-easycrypt/scripts/verify-all.sh
```

The aggregate run completed successfully:

```text
PASS baseline verification
PASS LaTeX research notes build
PASS read-only roots unchanged after verification
RESULT PASS authored-targets=44 cache=-no-eco
```

The complete compact record is in `logs/verify-all-summary.txt`.

## Week 10 single priority

Remain **CONTINUE-RANS**. The single first obligation is the actual encoder
outer-loop trace refinement and success-size derivation. Do not start the
`h` codec. Once the encoder postcondition compiles, use it and the already
proved actual copy theorem as the only input to the decoder trace invariant.
