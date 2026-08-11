# Week 10 report

Date: 2026-08-08

## Decision

Week 10 ends as **CONTINUE-ENCODER**.

The sprint added implementation-level semantic evidence beyond the Week 9
`bad in {0,1}` control theorem: the actual generated `_rans_encode` now has a
compiled nested-loop proof whose invariant preserves the bytes written by the
inner normalization loop through `segment_matches`, preserves the unwritten
prefix through `prefix_frame`, and proves W64 cursor no-underflow.  A direct
Hoare corollary also derives the success size range
`4 <= 1024 - returned_off <= 1024` from the actual returned state.

The mandatory parent claim is nevertheless still **PARTIAL**.  No compiled
theorem yet identifies the whole actual suffix with
`trace_bytes(symbol_list_of_array(symbols0))`.  In particular, the actual
outer-loop word update has not been composed with the pure suffix recurrence,
and the four actual final-state writes have not been composed with the outer
normalization suffix in one generated-procedure postcondition.

## Baseline

The pre-edit Week 10 baseline is preserved in
`logs/week10-baseline-summary.txt`:

```text
RESULT PASS authored-targets=44 cache=-no-eco
```

It included focused extraction, deterministic table-certificate
regeneration, selected baselines, source drift, and the Week 1--9 LaTeX notes.

## Fresh-compiled BArray/list bridge

`Mode2RansArrayListBridge.ec` defines:

```text
symbol_list_of_array(a) = map W8.to_uint (take 1024 (to_list a))
symbol_suffix(a,i)      = drop i (symbol_list_of_array a)
segment_matches(a,p,bs)
prefix_frame(before,after,p)
```

The fresh-compiled lemmas establish the 1024-element size, suffix base and
cons recurrence, canonicality of every suffix, pointwise segment access,
prepend/set and concatenation rules, prefix-frame preservation, W64 decrement
no-wrap, and the one-symbol `encode_trace` recurrence.  The bridge has an
explicit satisfiability witness and does not expand 1024 concrete elements.

## Fresh-compiled word-step bridge

`Mode2RansEncoderWordStep.actual_mode2_encoder_word_step_correct` proves:

```text
0 <= s < 13 /\ 1 <= W32.to_uint x < hbz_xmax(s)
  => actual_mode2_encoder_word_step(x,s)
       = W32.of_int(hbz_fast_encode_step(W32.to_uint x,s))
```

`actual_mode2_encoder_word_step` models the exact generated table fields,
64-bit reciprocal product and high-half extraction, shift ladder, complement,
bias, and W32 additions.  The proof uses the literal mode-2 table certificate
and proves the lookup, multiplication, quotient and no-wrap bounds.  This is a
word-level equality lemma; it is not by itself a Hoare theorem over the outer
generated loop.

## Pure 0/1/2-byte progress and serialization

`Mode2RansEncoderInnerProgress.ec` proves the pure inner progress relation:

- normalization length is 0, 1 or 2 under the Week 9 trace-state bound;
- `inner_state_after` follows repeated division by 256;
- `inner_written_suffix` grows by the exact low byte;
- `inner_progress_segment_step` preserves `segment_matches` when the cursor is
  decremented and the actual byte word is stored.

`Mode2RansEncoderSerialization.ec` proves that four concrete `set8` operations
encode `serialize32_le(W32.to_uint x)`, frame every outside byte, preserve the
prefix below the serialization start, and imply the scalar success-size
arithmetic.  These lemmas are ready for the final outer-loop consequence but
are not presented as the actual `_rans_encode` postcondition.

## Actual generated inner-loop evidence

`Mode2RansEncoderActualInner.actual_rans_encode_inner_no_underflow` directly
targets:

```text
RansEncodeTarget.M._rans_encode
```

with the concrete mode-2 encoder table, `count=1024`, and a canonical symbol
array.  Its returned postcondition is:

```text
returned_bad <> 0
\/
(returned_bad = 0 /\ W64.to_uint(returned_off) <= 1020).
```

Inside that actual procedure proof, the nested generated normalization loop
is verified with both:

```text
encoder_inner_phase_inv x_max x off
encoder_inner_segment_inv x_max x off encp
```

`encoder_inner_segment_step` proves that the exact generated transition

```text
off <- off - 1;
encp[off] <- truncateu8(x);
x <- x >> 8
```

prepends the corresponding byte to `encoder_phase_written`, preserves
`segment_matches`, and frames all lower indices.  This is an actual-loop
invariant, not an independent observation wrapper.

The invariant currently uses a conservative finite phase `0..4`, justified
from W32 finiteness and positive `x_max`.  The already-proved pure `0..2`
bound has not yet been installed into the actual outer-state invariant.
Therefore `OBL-RANS-ACTUAL-INNER-NORMALIZE` is recorded as **PARTIAL with a
proved actual byte/frame step**, rather than as the complete pure-trace
normalization refinement.

`actual_rans_encode_success_size_bound` is a second direct Hoare theorem over
the same generated procedure.  It preserves the actual failure branch and,
on `returned_bad=0`, proves:

```text
0 <= returned_off <= 1020
4 <= 1024 - returned_off <= 1024.
```

It is partial correctness.  It does not prove that the success branch is
reachable or that `_rans_encode` terminates on any concrete input.

## Exact residual

The unproved required conjunction is:

```text
segment_matches(
  returned_encp,
  W64.to_uint(returned_off),
  trace_bytes(symbol_list_of_array(symbols0)))
/\
W64.to_uint(returned_off)
  + size(trace_bytes(symbol_list_of_array(symbols0))) = 1024
/\
prefix_frame(enc0,returned_encp,W64.to_uint(returned_off)).
```

The next proof must strengthen the actual outer invariant, on its live branch,
with all of the following at once:

```text
i in [0,1024]
x = encode_trace(symbol_suffix(symbols0,i)).state
off + size(encode_trace(symbol_suffix(symbols0,i)).bytes) = 1024
segment_matches(encp,off,encode_trace(symbol_suffix(symbols0,i)).bytes)
prefix_frame(enc0,encp,off).
```

The current actual inner invariant supplies the byte-write/frame transition,
and the word-step and suffix-recurrence lemmas supply the mathematical next
state.  The missing compiled edge is their application through the generated
table-load/protect/reciprocal-shift control sequence in one outer iteration.

## Failure branch and non-vacuity

- Encoder success is not a precondition.  Both direct actual Hoare theorems
  retain `returned_bad <> 0` as a disjunct.
- The generated `off < 4` transition sets `bad=1`; the success-only invariant
  is not required after that transition.
- Array/list, word-step, inner-progress, serialization, and canonical symbol
  premises have compiled witnesses.
- No EasyCrypt theorem proves the all-6 actual encoder returns `bad=0`.
  `OBL-RANS-ACTUAL-SUCCESS-WITNESS` remains `PARTIAL`.
- Local fixed-count encoder losslessness and Sign rejection-loop losslessness
  are distinct and neither is inferred here.

## Claim status

| Claim | Status | Week 10 evidence / residual |
| --- | --- | --- |
| `OBL-RANS-ARRAY-LIST-BRIDGE` | `PROVED` | exact 1024-element array/list/suffix and segment/frame lemmas |
| `OBL-RANS-ENCODER-WORD-STEP` | `PROVED (word-level)` | concrete mode-2 table reciprocal step equals pure fast step |
| `OBL-RANS-ACTUAL-INNER-NORMALIZE` | `PARTIAL` | actual loop preserves finite byte segment/frame and no-wrap; actual `0..2`/pure-trace identification remains |
| `OBL-RANS-FINAL-SERIALIZATION` | `PROVED (leaf)` | exact four-byte LE stores and frame; generated-procedure composition remains |
| `OBL-RANS-ENCODER-SUCCESS-SIZE` | `PROVED (actual partial correctness)` | actual failure/success disjunction; success implies offset and size range |
| `OBL-RANS-ENCODE-REFINEMENT` | `PARTIAL` | exact outer suffix/state relation absent |
| `OBL-RANS-ACTUAL-SUCCESS-WITNESS` | `PARTIAL` | no actual success/termination theorem |
| `OBL-RANS-CORE-INVERSE` | `PARTIAL` | decoder semantic refinement remains out of Week 10 scope |
| `OBL-SIG-HBZ-ENCODE-DECODE` | `PARTIAL` | full wrapper and actual success witness remain |

## Verification and next gate

All Week 10 files are in `manifests/proof-targets.txt` and are compiled with
`-no-eco`.  The aggregate verifier additionally checks their theorem surfaces,
focused extraction and concrete table-certificate regeneration, proof holes,
authored axioms, debug declarations, source drift, baselines, and LaTeX.

The final command and result were:

```text
./haetae-topdown-easycrypt/scripts/verify-all.sh
RESULT PASS authored-targets=50 cache=-no-eco
```

The selected upstream baselines, final read-only-root comparison, and LaTeX
undefined-reference/citation/error checks all passed.  The resulting research
notes PDF has 33 pages at `latex/main.pdf`.

Week 11 must remain **CONTINUE-ENCODER** and target only the outer one-symbol
semantic transition plus final generated serialization composition.  The
decoder lane remains NO-GO until the exact actual suffix relation above
fresh-compiles.
