# Week 8 rANS proof design

Date: 2026-08-08

## Scope

This note fixes the Week 8 proof decomposition for
`OBL-SIG-HBZ-ENCODE-DECODE`.
It is not a claim that the full HBZ inverse is already proved.

## Separation of edges

The Week 8 HBZ path is decomposed into four layers.

1. coefficient/symbol leaves
2. concrete table certificate
3. rANS core inverse
4. actual full wrapper composition

Layers 1 and 2 are closed.  Layer 3 is closed only for the pure single-step
arithmetic; the generated normalization loops and layer 4 remain open.

## Actual constants

The mode-2 HBZ lane uses:

- `count = 1024`
- `m = 13`
- `offset = 6`
- `scale = 1024 = 2^10`
- initial/final rANS state `2^23 = 8388608`

These belong to the actual Week 8 focused extraction, not an abstract
reparameterization.

## Leaf layer

The leaf layer is handled by:

- `Mode2HbzPrepare`
- `Mode2HbzApply`
- `Mode2HbzLeafRoundTrip`

This establishes:

- canonical HBZ coefficient range
- exact symbol mapping `signed(hbz[i]) + 6`
- exact inverse `symbol - 6`
- local tail frames

The leaf layer is independent of rANS buffer success.

## Concrete table certificate

The table certificate is split into:

- `Mode2HbzTableCertificate`
  for the concrete mode-2 arithmetic formulas and generic certificate
- `Mode2HbzSymbolWordsGenerated`
  for the actual-array corollary that connects
  `SignaturePackMode2Target` / `SignatureUnpackMode2Target`
  arrays to the generic certificate predicate

This split is intentional:

- generic arithmetic lemmas stay small and reviewable
- the bulk actual-array proof is deterministic and regenerable
- the external generator is not trusted because EasyCrypt re-checks the
  produced proof file

## Core inverse target

The intended Week 8/9 rANS core theorem family is:

- encoder-step quotient/remainder correctness
- decoder interval lookup correctness
- single-step encode/decode inverse
- reverse-encode / forward-decode list invariant
- actual encoder refinement to the pure model
- actual decoder refinement to the pure model

The key remaining risk is not the coefficient mapping but:

- actual byte normalization and suffix layout
- loop invariants strong enough to connect reverse encode to forward decode

`Mode2RansCore` now closes the arithmetic sub-edge.  In particular,
`pure_rans_step_inverse` proves the quotient/remainder inverse and
`hbz_fast_step_decode_inverse` uses the concrete reciprocal certificate to
replace the mathematical encoder step on
`1 <= x < hbz_xmax(s)`.  This result deliberately contains no generated
procedure and is not labeled as actual rANS refinement.

## Failed generated-loop prototypes

Two prototypes were time-boxed and then removed from the authored target set
because neither reached a fresh-compiling theorem.

- The actual encoder prototype opened `RansEncodeTarget.M._rans_encode`.
  A weak final-state theorem first failed because the outer loop was not the
  last command, then exposed the nested normalization loop after `wp`.  After
  separating the branch and inner loop, automation stalled inside the
  normalization-loop invariant.  The missing fact is the backward byte-stack
  relation, not the already-proved reciprocal quotient.
- The actual `__copy_encoded_suffix` prototype maintained pointwise copied
  bytes and an output tail frame.  Its body invariant discharged, but fresh
  compilation repeatedly stalled at the quantified loop-exit projection.
  No uncompiled `.ec` target or theorem name is retained as evidence.

Adding another observation wrapper or a larger `inline; sim` layer is
rejected.  Week 9 should define one explicit product state containing the
encoder cursor, decoder cursor, reversed normalization-byte segment, and
current rANS state, then refine both generated loops to it.

## Wrapper composition boundary

The full HBZ parent theorem must remain success-conditioned:

```text
canonical_hbz_mode2(hbz) /\ actual encode size <> 0
  =>
decode bad = 0 /\
decoded_hbz[0,1024) = hbz[0,1024)
```

or an equivalent disjunction with `size = 0`.

This success condition must come from the actual encoder result. It may not be
assumed as a separate axiom.

## Current Week 8 stop rule

The concrete actual-array table certificate and the pure step inverse compile,
but the actual rANS core inverse does not.  The decision is therefore
`CONTINUE-RANS`: Week 9 remains on the single normalization-byte-stack edge
and does not widen to the `h` codec.

## Week 9 trace representation

Week 9 fixes one common pure meaning rather than attempting encoder/decoder
lockstep. For a canonical symbol list `symbols`:

- `xs = trace_states symbols`, with `xs[count] = 2^23` and `xs[0]` the
  serialized initial decoder state;
- `trace_segments symbols` stores each symbol's 0/1/2 normalization bytes in
  decoder-consumption order;
- `cuts = cuts_from 4 trace_segments`, so `cuts[0] = 4` and each interval
  `[cuts[k], cuts[k+1])` is the segment consumed after decoder symbol `k`;
- `trace_bytes` is `serialize32_le(xs[0])` followed by the flattened
  normalization segments.

`Mode2RansByteStack` compiles the structural and arithmetic lemmas for this
representation. In particular, `renorm_bytes_readback` proves that appending
the segment to the reduced state reconstructs the pre-normalized boundary
state, while `trace_head_decodes_to_reduced` and
`trace_head_normalization_readback` connect that fact to the already-proved
mode-2 fast step.

## Week 9 normalization and byte order

For `2^23 <= x < 2^31` and `xmax(s) >= 2^21`, the chosen normalization model
has length 0, 1, or 2. The two-byte segment is `[high, low]` in the final
suffix: the encoder writes low first while moving the cursor backwards, so
the decoder encounters high first and low second. `Mode2RansNormalization`
proves the corresponding W32 facts:

- right shift by 8 is integer division by 256;
- `truncateu8` is remainder modulo 256;
- decoder shift/or is `256*x+b` under the stated bound;
- one- and two-byte append reconstruct the original W32 word;
- one/two W64 cursor decrements have no underflow under explicit bounds.

These are pure/word leaf theorems. They are not presented as an isolated
generated-loop theorem because the normalization loop is nested inside
`_rans_encode` and `_rans_decode`.

## Actual procedure progress

`Mode2RansSuffixCopy.copy_encoded_suffix_correct` now closes the Week 8 copy
residual on the actual `HbzFullEncodeTarget.M.__copy_encoded_suffix`. Its
invariant proves the pointwise source slice and frames output indices
`[size,2048)`.

The two generated loops have direct, fresh-compiled control theorems:

- `actual_rans_encode_mode2_control` fixes the actual HBZ encoder table,
  `count=1024`, canonical symbol bytes, and proves the published `bad` is 0 or
  1;
- `actual_rans_decode_mode2_control` fixes the actual symbol/dsym tables and
  decoder state fields and proves the published `bad` is 0 or 1.

They deliberately do not use the word “refines” in their theorem names. At
the Week 9 boundary, the semantic postconditions required by
`OBL-RANS-ENCODE-REFINEMENT` and `OBL-RANS-DECODE-REFINEMENT` were still
open.

`Mode2RansActualHarness.run` is the requested unary execution boundary. It
directly calls the actual encoder, conditionally calls the actual suffix copy
with returned `off` and `size`, initializes decoder fields to `(1024,size,13)`,
and directly calls the actual decoder. The compiled harness theorem establishes
only branch reachability and exact decoder input-field initialization.

## Exact residual after Week 9

The failed strategy was to let a weak outer-loop invariant plus automation
discover the nested byte relation. It can prove the control bit is in
`{0,1}`, but it cannot establish either of these missing edges:

1. actual encoder post-state implies `valid_rans_trace` for the input symbols;
2. actual decoder started from that copied trace produces the original symbols,
   final state `2^23`, and consumed offset `size`.

The next attempt must add the explicit array/list bridge to the actual outer
loop invariants. It must not add an arbitrary trace premise, assume decoder
success, or replace the actual copy with a constructed buffer.

Accordingly Week 9 remains `CONTINUE-RANS`. The narrower single next edge is
the actual encoder outer-loop invariant linking `(i,x,off,encp)` to the suffix
of `trace_states`, `trace_cuts`, and `trace_bytes`. Decoder refinement follows
only after that encoder postcondition compiles.

## Week 10 encoder-only implementation boundary

Week 10 first closes the representation lemmas that Week 9 intentionally left
implicit. `Mode2RansArrayListBridge` defines the actual-array symbol list,
suffixes, byte-segment equality, and prefix frame. It proves the suffix cons
recurrence and an `encode_trace` extension usable by one outer iteration.

The generated reciprocal update is factored into
`actual_mode2_encoder_word_step`. The theorem
`actual_mode2_encoder_word_step_correct` checks the literal mode-2 esym fields,
high-half W64 product, shift ladder, quotient, complement and bias against the
pure fast step. This avoids reproving the same 13-way table arithmetic inside
each loop iteration.

The actual nested normalization loop is no longer treated only as control.
`Mode2RansEncoderActualInner.actual_rans_encode_inner_no_underflow` directly opens
the generated `_rans_encode` and runs the nested loop with a compiled
`encoder_inner_segment_inv`. Each actual `off--`, `set8`, and `x>>8`
transition prepends the exact shifted byte to a `segment_matches` list and
preserves the lower prefix frame. This is the first generated-loop byte
semantics result.

The invariant is intentionally reported as partial. It tracks only the bytes
emitted by the current inner call and uses a conservative phase bound `0..4`.
It does not carry the already encoded tail
`encode_trace(symbol_suffix(symbols0,i+1)).bytes`, nor does it identify the
exit phase with `mode2_normalization_len` and
`mode2_normalization_bytes`. The pure 0/1/2 exit lemmas exist in
`Mode2RansEncoderInnerProgress`, but their actual-loop composition is the first
remaining edge.

The precise next invariant must therefore be tail-aware:

```text
segment_matches(
  encp,
  off0-k,
  encoder_phase_written(x0,k) ++ encode_trace(tail).bytes)
```

together with `x0=encode_trace(tail).state` and
`off0+size(encode_trace(tail).bytes)=1024`. At inner-loop exit, the pure
`inner_*_total` lemmas can then replace the phase prefix by the exact
normalization list. Only after that rewrite can the concrete word-step theorem
and `encode_trace_suffix_extension` re-establish the outer live invariant.

Final little-endian serialization and scalar size arithmetic compile as leaf
theorems. Moreover `actual_rans_encode_success_size_bound` directly proves the
actual generated success/failure disjunction and success range. What remains
is the combined generated-procedure byte postcondition, not the size range.

Hence Week 10 is `CONTINUE-ENCODER`: there is stronger actual semantic
evidence, but no whole suffix equality and no actual success witness. Decoder
semantics remains deliberately untouched.

## Week 11 actual encoder refinement

The Week 10 local snapshot was replaced by two initial-input-relative
predicates, `encoder_outer_tail_inv` and `encoder_inner_tail_inv`. Their common
semantic object is the pure suffix of the actual input array. This makes each
generated inner write preserve
`inner_written_suffix ++ encode_trace(tail).bytes`, rather than merely a local
byte list.

The proof is deliberately layered:

1. `encoder_inner_tail_exit_exact` closes the actual 0/1/2 normalization exit;
2. `generated_loaded_nested_word_update` rewrites the generated table fields,
   reciprocal product and nested shift ladder to the certified word step;
3. `encoder_generated_success_outer_post` composes the generated body with the
   pure state/byte recurrence and cursor arithmetic;
4. the actual outer while derives `i=0` on its live success exit while retaining
   an unconstrained trace for `bad=1`;
5. `generated_encoder_outer_finalize_success` prepends the little-endian state
   written by the four actual stores;
6. `actual_rans_encode_trace_closure` packages the direct generated-procedure
   success/failure postcondition, and
   `actual_rans_encode_trace_refinement` exposes the exact suffix corollary.

No encoder wrapper, arbitrary trace witness, success precondition, or 1024-way
unrolling is introduced. A one-shot tactic was rejected because it loses the
pure tail at the nested-loop boundary; a large SMT goal over the generated
shift ladder was replaced by rewriting the already proved generated word
equality. The result is success-conditioned Hoare partial correctness, not a
termination or successful-input theorem.

The proof dependency now has only one semantic core edge left:

```text
actual encoder trace [PROVED]
  -> actual suffix copy [PROVED]
  -> actual decoder consumes the same trace [PARTIAL]
  -> actual rANS core inverse [PARTIAL]
```

Week 12 must address only the decoder trace invariant. Full HBZ wrappers and
all wider codec/security lanes remain downstream.

## Week 12: actual decoder refinement

Week 12 refines the generated decoder to the same pure trace without changing
the Week 9 byte-stack representation. For
`syms = symbol_list_of_array expected_symbols`, the reference boundary at
symbol index `i` is:

```text
state(i)   = decoder_state_at syms i
cursor(i)  = decoder_cursor syms i
segment(i) = decoder_segment_at syms i
```

The boundary equations are compiled: `cursor(0)=4`,
`cursor(i+1)=cursor(i)+size(segment(i))`,
`cursor(1024)=size(trace_bytes syms)`, `state(0)` is the serialized
`encode_trace` head, and `state(1024)=2^23`.

The actual outer invariant `decoder_outer_trace_live` binds the generated
`i`, `x`, `off`, `bad`, output array, buffer, state fields, and literal tables
to this reference. It preserves exact equality of the decoded prefix and a
frame over the remaining `[i,2048)` output. The actual inner invariant binds
`k = off-cursor(i)` to replay of the first `k` bytes of `segment(i)`. Concrete
state bounds restrict the segment to length 0, 1, or 2; the generated guard is
proved equivalent to whether another segment byte remains.

The concrete table bridge is split from the loop proof. It proves that the
actual `x & 1023` packed-halfword lookup returns the expected symbol and that
the actual `dsyms_words` arithmetic equals the pure reduced decoder state.
This avoids 13-way table reasoning inside each loop iteration and introduces
no compatibility assumption.

The direct theorem is:

```text
actual_rans_decode_trace_refinement
  : hoare [RansDecodeTarget.M._rans_decode :
      actual concrete bindings and exact trace input
      ==> bad=0 /\ off=encoded_size /\
          decoded prefix equality /\ decoded tail frame]
```

The initial four bytes are parsed by the generated code and shown to equal the
pure trace head. At outer exit, `decoder_outer_trace_exit_components` proves
`i=1024`, `x=2^23`, and `off=encoded_size`; these facts discharge the actual
final-state and consumed-size reject tests. Internal `x` is therefore a proof
fact, not an invented ABI output.

A monolithic `inline; sim` proof and an extension of the control-only theorem
were rejected because neither preserves the variable-length normalization
cursor and output frame. The adopted decomposition uses cursor equations,
concrete word-step rewrites, an inner replay invariant, an outer prefix/frame
invariant, and a final consequence step.

This theorem is exact-trace partial correctness. It neither proves decoder
termination nor supplies actual encoder success. The remaining core edge is
not decoder semantics: it is the actual harness composition that derives the
decoder's pointwise exact-buffer relation from the already proved encoder
segment and actual suffix copy. Until that compiles, the rANS core inverse and
full HBZ parent remain `PARTIAL`.

## Week 13: actual encoder/copy/decoder composition

Week 13 closes the remaining core edge without unfolding any of the three
generated loops again. The shared semantic object remains
`trace_bytes(symbol_list_of_array symbols)`, and the composition proceeds
through four explicit interfaces:

```text
actual encoder segment_matches
  -> actual copy slice_eq
  -> copied segment_matches at offset zero
  -> exact_decoder_segment_input
  -> actual_mode2_decoder_trace_input
```

`copied_suffix_is_exact_trace` is the array adapter: for every trace index it
uses the copy theorem's pointwise source slice and the encoder theorem's
pointwise trace equality. `trace_bytes_trace_segment_nth` then relates a
decoder cursor plus an intra-segment index to the same global trace-list
index. This yields `segment_matches_implies_exact_decoder_segment_input`, so
the Week 12 per-read relation is a consequence of the copied post-state and is
not a new premise or buffer witness.

The harness computes size as a W64 subtraction. The lemma
`encoder_success_size_word_bridge` first derives `off <= 1020` and
`off + trace_size = 1024` from the actual encoder success postcondition, then
uses unsigned subtraction under that proved order to establish:

```text
uint(W64.of_int 1024 - encoder_off) = trace_size
W64.of_int 1024 - encoder_off       = W64.of_int trace_size
4 <= trace_size <= 1024
```

The three generated state stores are represented exactly by
`configured_decoder_state`; `configured_decoder_state_fields` proves the
result has `(count,size,m)=(1024,trace_size,13)`. Together with the copied
segment, this constructs `actual_mode2_decoder_trace_input` rather than
assuming it.

`actual_rans_encode_copy_decode_inverse` is the final Hoare theorem over the
existing `Mode2RansActualHarness.run`. Its proof calls, in order,
`actual_rans_encode_trace_refinement`, `copy_encoded_suffix_correct`, and
`actual_rans_decode_trace_refinement`. The actual encoder's returned `bad`
selects the branch. Failure retains `decoder_ran=false`, the initial decoded
array, and the initial decoder state. Success runs the actual copy and decoder,
proves decoder `bad=0` and exact consumption, recovers all 1024 symbols, and
retains the decoded tail.

A large `inline; sim` proof was rejected because it would duplicate the
already compiled encoder and decoder loop invariants. Passing either copied
trace equality or decoder byte reads as a harness precondition was also
rejected because it would leave the implementation-composition edge open.
The chosen proof is top-level sequential theorem reuse with explicit array and
word adapters.

This establishes `OBL-RANS-CORE-INVERSE` only as success-conditioned partial
correctness. The harness precondition is satisfiable, but the theorem does not
establish encoder success reachability or procedure termination. It is also
not the production full-HBZ wrapper theorem. Week 14 must compose this core
with the already proved prepare/apply inverse at actual
`_encode_hb_z1_full`/`_decode_hb_z1_full` boundaries.

## Week 14 production lift

`signature_pack_unpack_hbz_full_actual_exact` closes that production wrapper
boundary. It proves that the production SignaturePack/Unpack harness and the
focused full-HBZ harness expose equivalent actual `_encode_hb_z1_full` and
`_decode_hb_z1_full` procedures. The Hoare corollary
`signature_pack_unpack_hbz_full_inverse_mode2` keeps the exact encoder-size
split visible:

- `size = 0`: decoder skipped, initialized buffers preserved;
- `size <> 0`: decoder runs, `bad = 0`, the decoded prefix and tail frame are
  proved, and a concrete `prepared_symbols` witness supplies the trace bytes.

This is success-conditioned partial correctness only. The fixed all-6 theorem
now excludes failure for terminating runs; it does not establish termination,
losslessness, or non-vacuous reachability. The `h` codec is now the Week 16
target only.

## Week 15 witness

`Mode2RansActualSuccessWitness.actual_rans_encode_all_six_success` proves the
fixed all-6 witness at the actual `RansEncodeTarget.M._rans_encode` surface.
The fixed-input HBZ lift is carried by
`full_rans_encode_all_six_success`,
`actual_encode_hb_z1_full_zero_success`,
`signature_pack_hbz_zero_success_mode2`,
`actual_hbz_full_encode_decode_zero_success_mode2`, and
`signature_pack_unpack_hbz_zero_success_mode2`.

This is fixed-input Hoare partial correctness: every terminating run has the
success result. It is not a termination, losslessness, probability-one, or
non-vacuous execution theorem.
