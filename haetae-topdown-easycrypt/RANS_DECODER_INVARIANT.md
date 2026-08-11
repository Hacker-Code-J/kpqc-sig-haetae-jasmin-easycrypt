# Week 12 actual rANS decoder invariant

## Claim boundary

The Week 12 target is the generated procedure
`RansDecodeTarget.M._rans_decode`.  The compiled theorem is
`actual_rans_decode_trace_refinement` in
`easycrypt/refinement/sign/Mode2RansDecoderTopHoare.ec`.

It is a Hoare partial-correctness theorem.  It says what every terminating
execution does when its input buffer is the exact mode-2 `trace_bytes` for a
canonical 1024-symbol array.  It does not prove that the procedure terminates,
that the encoder reaches its success branch, or that the full HBZ wrapper
succeeds.

## Reference state and cursor

For `syms = symbol_list_of_array expected_symbols`, iteration `i` uses:

```text
state(i)  = decoder_state_at syms i
cursor(i) = decoder_cursor syms i
segment(i)= decoder_segment_at syms i
```

The compiled cursor lemmas establish:

```text
cursor(0)    = 4
cursor(i+1)  = cursor(i) + size(segment(i))
cursor(1024) = size(trace_bytes syms)
state(0)     = fst(encode_trace syms)
state(1024)  = 2^23
```

`decoder_cursor_segment_before_final` also proves that every byte read inside
`segment(i)` is before the exact encoded-size boundary.

## Outer invariant

`decoder_outer_trace_live` binds the actual generated variables to the
reference execution.  Its live branch contains all of the following:

```text
0 <= uint(i) <= 1024
bad = 0
x = W32.of_int(state(uint(i)))
uint(off) = cursor(uint(i))
decoded[0..uint(i)) = expected_symbols[0..uint(i))
decoded[uint(i)..2048) = decoded0[uint(i)..2048)
count = 1024
size_in = state0[1]
m = 13
actual symbol_words and dsyms_words tables are bound
```

The input state and encoded buffer are also preserved in the invariant.  The
outer-loop guard is converted from the generated W64 comparison to
`uint(i) < 1024` by `decoder_outer_guard_index`.

## Concrete table and word-step bridge

The generated body computes the symbol-table index from `x & 1023`, chooses
the appropriate packed halfword, stores the recovered byte, loads the packed
decoder word, and computes the reduced state.  The following compiled lemmas
connect those exact expressions to the mathematical step:

- `generated_decoder_lookup_word_from_mode2`;
- `generated_decoder_symbol_from_mode2`;
- `generated_decoder_word_update_from_mode2`;
- `generated_decoder_symbol_expected`;
- `generated_decoder_word_update_matches`;
- `decoder_outer_to_inner_trace_actual_loaded`.

The concrete `jmode2_hb_z1_symbol_words` and
`jmode2_hb_z1_dsyms_words` arrays are used in these statements.  There is no
table-compatibility axiom.

## Inner normalization invariant

After the symbol word-step, `decoder_inner_math` sets

```text
j         = uint(i)
tail      = symbol_suffix(expected_symbols,j+1)
tailstate = decoder_state_at syms (j+1)
segment   = decoder_segment_at syms j
k         = uint(off) - cursor(j)
```

and maintains:

```text
0 <= k <= size(segment)
uint(off) = cursor(j) + k
x = W32.of_int(decoder_replay_prefix(tailstate,s,k))
```

The concrete mode-2 bound proves `size(segment) <= 2`.  The generated guard
`zeroextu64(x) < 2^23` is equivalent to `k < size(segment)`:

- length 0: the guard is false immediately;
- length 1: one exact buffer byte is appended and the guard becomes false;
- length 2: two exact bytes are appended before the guard becomes false.

`decoder_inner_trace_step` proves the consuming transition and preserves the
decoded prefix/tail.  `decoder_inner_trace_stop` handles the final no-consume
guard check.  `decoder_inner_math_exit` and
`decoder_inner_trace_exit_to_outer` establish the next `state(i+1)` and
`cursor(i+1)` boundary.

## Initial parse and final checks

`generated_decoder_parse32_from_trace` derives the actual four-byte
little-endian parse from `segment_matches buffer0 0 (trace_bytes syms)`.
The state bounds prove that neither initial reject branch can execute.

At outer-loop exit, `decoder_outer_trace_exit_components` derives:

```text
i = 1024
x = W32.of_int(2^23)
off = W64.of_int(encoded_size)
size_in = W64.of_int(encoded_size)
bad = 0
decoded[0..1024) = expected_symbols[0..1024)
decoded[1024..2048) = decoded0[1024..2048)
```

Consequently both generated final checks pass.  The actual stores
`statep[0] <- off` and `statep[1] <- bad` yield the published postcondition.

## Non-vacuity and remaining edge

The theorem premise does not contain decoder success, decoded equality, or a
post-state observation.  It contains the exact encoded trace and its concrete
state/table bindings.  Week 11's actual encoder theorem and the actual suffix
copy theorem are intended to construct those premises on the encoder-success
branch.  The final list/slice-to-decoder-read adapter and sequential harness
composition are not yet compiled, so `OBL-RANS-CORE-INVERSE` remains
`PARTIAL`.

No actual encoder-success witness or local encoder/decoder losslessness theorem
is available.  `OBL-RANS-ACTUAL-SUCCESS-WITNESS` therefore remains `PARTIAL`.
