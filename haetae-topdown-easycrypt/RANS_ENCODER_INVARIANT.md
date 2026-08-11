# Mode-2 actual RANS encoder invariant

This document records the Week 10 proof design and its compiled boundary.  The
operational claim status remains in `CLAIM_LEDGER.md`.

## Index convention

For the fixed mode-2 count `N=1024`:

```text
symbol_list_of_array(a) = [uint(a[0]), ..., uint(a[1023])]
symbol_suffix(a,i)      = drop i (symbol_list_of_array(a))
```

The generated encoder starts at `i=N` and decrements `i` before reading a
symbol.  Thus the live outer invariant at index `i` describes the already
processed suffix `symbol_suffix(symbols0,i)`.  At termination `i=0`, it
describes the full symbol stream.

## Required live outer invariant

The target success-only live invariant is:

```text
0 <= uint(i) <= N
x = encode_trace(symbol_suffix(symbols0,uint(i))).state
uint(off) + size(encode_trace(symbol_suffix(symbols0,uint(i))).bytes) = N
segment_matches(
  encp, uint(off),
  encode_trace(symbol_suffix(symbols0,uint(i))).bytes)
prefix_frame(enc0,encp,uint(off))
4 <= uint(off).
```

The failure branch deliberately keeps only `bad=1` and control facts.  It does
not require a trace relation after buffer exhaustion.

## Compiled array/list recurrence

`Mode2RansArrayListBridge` proves:

```text
symbol_suffix(a,1024) = []
symbol_suffix(a,i) = uint(a[i]) :: symbol_suffix(a,i+1)
```

and splits the corresponding trace extension into:

```text
encode_trace(s::tail).state
  = hbz_fast_encode_step(normalized_state(encode_trace(tail).state,s),s)

encode_trace(s::tail).bytes
  = normalization_bytes(encode_trace(tail).state,s)
      ++ encode_trace(tail).bytes.
```

The bridge is range-based; it does not unroll 1024 elements.

## Compiled actual inner invariant

`Mode2RansEncoderActualInner` opens the generated `_rans_encode`; the reusable
phase and segment predicates live in `Mode2RansEncoderTrace`.

The nested generated loop is checked with a phase witness `(x0,off0,k)`:

```text
0 <= k <= 4
uint(off) = off0-k
uint(x) = encoder_phase_state(uint(x0),k)
segment_matches(encp,off0-k,encoder_phase_written(uint(x0),k))
prefix_frame(before,encp,off0-k).
```

`encoder_phase_written` is in decoder address order.  If the generated loop
writes the low byte and decrements its cursor, the new byte is prepended to the
list.  The proof uses the exact `BArray2048.set8` and W64 subtraction from the
generated program.  `before` is the array at entry to that particular inner
loop, so this invariant proves local write semantics and frame, not the full
outer accumulated trace.

The current `0..4` phase is a conservative W32 termination bound.  The pure
mode-2 trace separately proves normalization length `0..2`; installing
`x0 = encode_trace(tail).state` and `x_max = hbz_xmax(s)` in the actual outer
invariant is the remaining step needed to identify the phase list with
`mode2_normalization_bytes(x0,s)`.

## Word-step bridge

After normalization, the generated code reads four encoder-table words and
computes the quotient using a reciprocal high product and a shift ladder.
`actual_mode2_encoder_word_step_correct` proves, for the literal mode-2 table:

```text
actual_word_step(x,s)
  = W32.of_int(hbz_fast_encode_step(W32.to_uint(x),s)).
```

The lookup index is `4*s`; the proof discharges table bounds, packed
frequency/complement fields, reciprocal quotient exactness, W64 product
bounds, and W32 no-wrap.  The remaining procedural edge is to rewrite the
actual variables loaded by `_rans_encode` to the arguments of this lemma
after the protect/declassify erasures.

## Final serialization

On success the generated procedure subtracts four from `off` and performs four
little-endian `set8` writes.  The compiled leaf theorem proves those writes are
exactly:

```text
serialize32_le(W32.to_uint(x))
```

and frame all other indices.  Given the target live outer invariant, the final
composition should use `segment_matches_cat` to derive:

```text
serialize32_le(x) ++ encode_trace(all_symbols).bytes
  = trace_bytes(all_symbols).
```

The scalar arithmetic is already compiled: live `off>=4` gives returned
`off'=off-4`, and `off + normalization_size = 1024` gives
`4 <= 1024-off' <= 1024`.

## Failed tactics and rejected shortcuts

- A one-shot `inline; sim` was not retried.  Reverse outer iteration and
  variable-length inner normalization do not form a lockstep relational loop.
- A larger proof-only encoder wrapper was not introduced.
- Encoder success, trace validity, output equality, and decoder success were
  not moved into preconditions.
- A 1024-iteration generated certificate was not used for the general proof.
- Strengthening the old `bad in {0,1}` theorem alone was insufficient; the
  byte segment and frame needed their own invariants.
- SMT was not asked to infer W64 decrement no-wrap or list prepend semantics;
  both are explicit lemmas.

## Week 11 single edge

The next proof should duplicate no new wrapper.  It should strengthen the
actual `_rans_encode` outer invariant with the five live facts above, apply
the compiled inner byte transition and word-step lemma for one symbol, and
finish by composing the actual final stores with the accumulated trace.  Only
after that theorem compiles should work begin on actual decoder semantics.

## Week 11 closure

Week 11 installs that invariant directly in the generated procedure. The live
outer predicate is:

```text
0 <= i <= 1024
x = encode_trace(symbol_suffix(symbols0,i)).state
off + size(encode_trace(symbol_suffix(symbols0,i)).bytes) = 1024
segment_matches(encp,off,encode_trace(symbol_suffix(symbols0,i)).bytes)
prefix_frame(enc0,encp,off)
4 <= off
```

The inner predicate no longer quantifies over an arbitrary `before` snapshot.
It preserves, from the original `enc0`, the exact segment

```text
inner_written_suffix(x0,s,k) ++ encode_trace(tail).bytes
```

at cursor `off0-k`. The actual guard and the proved mode-2 bound give
`k=mode2_normalization_len(x0,s)<=2` at exit. The generated table loads and
shift ladder then refine to `hbz_fast_encode_step`, and the one-symbol
recurrences rebuild the outer invariant for `symbol_suffix(symbols0,j)`.

At `i=0`, `generated_encoder_outer_finalize_success` composes the actual four
stores with the accumulated normalization suffix. The direct actual Hoare
theorem `actual_rans_encode_trace_closure` therefore proves exact full suffix,
cursor/length equality, size bounds and the initial-prefix frame on the
returned success branch. The failure branch requires no trace relation.

This closes `OBL-RANS-ENCODE-REFINEMENT` as success-conditioned partial
correctness. It does not prove that the generated loop returns or that any
concrete execution reaches `bad=0`; those are separate losslessness and
non-vacuity obligations.
