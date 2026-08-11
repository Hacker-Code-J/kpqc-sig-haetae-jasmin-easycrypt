# Week 9 rANS byte-stack invariant

Date: 2026-08-08

## Scope and status

This document records the common meaning used to compare the reverse actual
encoder with the forward actual decoder. The pure byte-stack and word-level
normalization facts compile. The two generated outer-loop refinements do not;
therefore `OBL-RANS-CORE-INVERSE` remains `PARTIAL`.

## Index convention

For `count = 1024` canonical symbols:

- `xs[count] = 2^23`;
- the encoder handles `j = count-1, ..., 0`;
- `xs[0]` is the state serialized into the first four decoder bytes;
- after decoding `k` symbols, the intended decoder state is `xs[k]`;
- `cuts[0] = 4`;
- `[cuts[k],cuts[k+1])` contains exactly the normalization bytes consumed
  after symbol `k`;
- `cuts[count]` is the total encoded size.

The EasyCrypt operations are `encode_trace`, `trace_states`,
`trace_segments`, `trace_cuts`, and `trace_bytes` in
`Mode2RansByteStack.ec`.

## Byte order

For two emitted bytes, let the pre-normalized word be
`x = 256^2*q + 256*hi + lo`. The actual encoder first writes `lo`, decrements
the cursor again, and then writes `hi`. Hence the final forward buffer segment
is `[hi,lo]`. The actual decoder performs:

```text
q --append hi--> 256*q+hi --append lo--> x.
```

This is compiled as `encoder_two_byte_decoder_order`; the one-byte case is
`decoder_append_encoder_byte`. `renorm_bytes_readback` gives the corresponding
integer-list theorem.

## State bounds

The certificate supplies positive mode-2 frequencies and

```text
xmax(s) = 2^21 * freq(s) >= 2^21.
```

Under `2^23 <= x < 2^31`, `renorm_len` is in `{0,1,2}` and the reduced state
satisfies `1 <= xr < xmax(s)`. The concrete fast step preserves
`2^23 <= x' < 2^31`; this is `normalized_fast_step_state_bounds`. Induction
over canonical symbol lists gives `encode_trace_state_bounds`.

The bound is mathematical evidence for termination of each normalization
segment, but no theorem in Week 9 promotes it to losslessness of the full
actual encoder.

## Intended actual encoder invariant

At actual outer-loop head with word counter `i`, live branch `bad=0` should
establish:

```text
0 <= to_uint(i) <= 1024
x = encode_trace(symbols[to_uint(i)..1024]).state
off + length(trace_bytes_without_state(symbols[i..])) = 1024
encp[off..1024) = trace_bytes_without_state(symbols[i..])
encp outside the written suffix is framed
4 <= off                         (before processing another live symbol)
```

The inner invariant additionally relates the number of shifts already
performed to the 0/1/2 prefix of `renorm_bytes`. The actual table fields must
be rewritten using `actual_mode2_hbz_esym_fields`, and the W32 arithmetic must
be linked to `hbz_fast_encode_step` before advancing from suffix `i+1` to
suffix `i`.

This invariant has not yet been discharged in EasyCrypt.

## Intended actual decoder invariant

At actual decoder outer-loop head with counter `i`:

```text
0 <= to_uint(i) <= 1024
symsp[0..i) = original_symbols[0..i)
to_uint(x) = xs[i]
to_uint(off) = cuts[i]
bufp[cuts[i]..size) = remaining trace bytes
bad = 0
```

Concrete `symbol_words` selects the original symbol from `x mod 1024`; the
concrete `dsyms` word provides its start/frequency; the already-proved pure
step obtains the reduced predecessor state; and the inner loop consumes
exactly `[cuts[i],cuts[i+1])` to reconstruct `xs[i+1]`.

At `i=1024`, the invariant should yield `x=2^23`, `off=size`, `bad=0`, decoded
symbol equality, and the unused output-tail frame. This refinement is also
open.

## Actual suffix copy

`copy_encoded_suffix_correct` is a generated-procedure Hoare theorem, not a
pure replacement. Its premises are:

```text
0 <= off0
0 <= n
off0 + n <= 2048
```

Its postcondition is exact `slice_eq enc0 result off0 n` together with
`suffix_frame out0 result n`. The proof uses explicit guard-exit, set8
extension, outside-index frame, and no-wrap lemmas. No constructed decoder
buffer is used.

## Failure and success

The actual harness does not assume encoder success. It branches on the
published encoder `bad` value:

```text
bad != 0  -> decoder_ran = false
bad = 0   -> actual copy; decoder state (1024,size,13); actual decode
```

The compiled control theorem does not prove `4 <= size <= 1024`. That bound
must be obtained from the actual encoder refinement. It also does not prove
decoder success, decoded equality, final state, or consumed size.

## Non-vacuity

The pure premises have compiled witnesses, including symbol 6 and state
`2^23`. The actual all-6 encoder success witness is still open as
`OBL-RANS-ACTUAL-SUCCESS-WITNESS`. A runtime log would not replace the missing
EasyCrypt theorem.

## Rejected proof shapes

- direct encoder/decoder lockstep: their directions and normalization-loop
  counts differ;
- 1024 generated unrollings: this would not provide a reusable invariant;
- an arbitrary decoder byte array: it would bypass the actual suffix copy;
- trace validity or decoder success as a precondition: this would restate the
  desired conclusion;
- a weak `bad in {0,1}` control theorem presented as implementation
  refinement: Week 9 records it only as a boundary result.
