# Week 11 actual RANS encoder trace-closure report

Date: 2026-08-08

## Decision

**GO-ENCODER.** `OBL-RANS-ENCODE-REFINEMENT` is now **PROVED as
success-conditioned partial correctness**. Week 12 may move to the single
actual-decoder trace-refinement edge. No decoder, full-HBZ, `h`, metadata,
highbits/LSB, MU, security-composition, or Sign-losslessness work was started.

## Baseline

The unmodified Week 10/Week 11-start baseline passed before proof edits:

```text
./haetae-topdown-easycrypt/scripts/verify-all.sh
RESULT PASS authored-targets=50 cache=-no-eco
```

The baseline summary is preserved in `logs/week11-baseline-summary.txt`
(SHA-256
`71d9edc5f2206a5afeb9adf1df184f7c30d1b098d5646dae7f42ecc2e8579917`).

## Compiled actual theorem

`Mode2RansEncoderActualTraceClosure.actual_rans_encode_trace_closure` directly
opens `RansEncodeTarget.M._rans_encode`:

```easycrypt
hoare [Encode._rans_encode :
  encp = enc0 /\
  statep = state0 /\
  symsp = symbols0 /\
  esymsp = SignaturePackMode2Target.jmode2_hb_z1_esyms /\
  count = W64.of_int mode2_hbz_count /\
  mode2_hbz_symbol_stream symbols0
  ==> encoder_trace_post enc0 symbols0 res]
```

The success/failure postcondition is based on the actual returned `bad`. It
does not receive encoder success or trace validity as a premise. The success
branch states:

```text
returned_bad = 0
0 <= uint(returned_off) <= 1020
4 <= 1024 - uint(returned_off) <= 1024
segment_matches(
  returned_encp,
  uint(returned_off),
  trace_bytes(symbol_list_of_array(symbols0)))
uint(returned_off) +
  size(trace_bytes(symbol_list_of_array(symbols0))) = 1024
prefix_frame(enc0,returned_encp,uint(returned_off))
```

`Mode2RansEncoderOuterRefinement.actual_rans_encode_trace_refinement` is the
fresh-compiled expanded corollary. It contains the actual generated procedure,
the actual symbol array, and the exact full suffix relation; it is not an
existential-trace or pure-only theorem.

## Proof decomposition

- Pure/list layer: the existing `symbol_suffix` and `encode_trace` recurrence
  is reused without re-proving Week 10.
- Tail-aware actual inner loop: `encoder_inner_tail_inv` relates every actual
  write to the initial `enc0` and
  `inner_written_suffix ++ encode_trace(tail).2`.
  `encoder_inner_tail_exit_exact` derives `k=normalization_len<=2` from the
  actual generated guard.
- Generated word/WP bridge: concrete table loads, protect erasures, reciprocal
  high-product, shift ladder, complement, bias and addition are rewritten by
  `generated_loaded_nested_word_update` and
  `generated_outer_word_update_matches`.
- One-symbol/outer closure: `encoder_generated_success_outer_post` rebuilds the
  exact pure state, bytes, cursor and prefix frame. `bad=1` deliberately drops
  the live trace relation.
- Generated final stores: `generated_encoder_outer_finalize_success` proves
  the four actual little-endian stores prepend the serialized state to the
  accumulated normalization suffix.

## Failed approaches and resolution

- Retaining the Week 10 arbitrary `before` snapshot could not connect local
  normalization bytes to the accumulated pure tail; it was replaced rather
  than extended.
- A one-shot expansion of the generated reciprocal shift ladder produced a
  large weakest-precondition expression. Rewriting the dedicated generated
  word-step theorem closed that edge once, outside repeated symbol cases.
- Automatic normalization left `W64.of_int 1024` as a modular expression at
  outer initialization. The canonical value and empty trace were proved
  explicitly.
- Large existential traces, success preconditions, proof-only encoder copies,
  and 1024-iteration unrolling were not used.

## Claim status

| Claim | Status | Boundary |
| --- | --- | --- |
| `OBL-RANS-ACTUAL-INNER-NORMALIZE` | `PROVED` | actual nested encoder loop, tail-aware exact exit |
| `OBL-RANS-FINAL-SERIALIZATION` | `PROVED` | composed with actual generated final stores |
| `OBL-RANS-ENCODE-REFINEMENT` | `PROVED` | success-conditioned Hoare partial correctness |
| `OBL-RANS-ACTUAL-SUCCESS-WITNESS` | `PARTIAL` | no terminating all-6 success theorem |
| `OBL-RANS-DECODE-REFINEMENT` | `PARTIAL` | only prior control evidence |
| `OBL-RANS-CORE-INVERSE` | `PARTIAL` | decoder semantic edge remains |
| `OBL-SIG-HBZ-ENCODE-DECODE` | `PARTIAL` | decoder, wrapper composition and witness remain |

## Partial correctness and non-vacuity

The theorem proves every terminating call satisfies the failure/success
disjunction. It does **not** prove that `_rans_encode` terminates, that the
success branch is reachable, or that all-6 symbols produce success. Thus the
input representation premises are satisfiable and the generated program is
real, but actual success-branch non-vacuity remains `PARTIAL`. This is local
encoder losslessness, not Sign rejection-loop losslessness.

No decoder success, HBZ round trip, canonical parsing, encoding zero-loss, or
security theorem follows from Week 11.

## Verification

The decisive commands are:

```sh
easycrypt compile -no-eco -script -timeout 5 \
  easycrypt/refinement/sign/Mode2RansEncoderActualTraceClosure.ec ...

easycrypt compile -no-eco -script -timeout 5 \
  easycrypt/refinement/sign/Mode2RansEncoderOuterRefinement.ec ...

./scripts/verify-all.sh
```

The final `verify-all.sh` checks all 57 authored targets, deterministic focused
extraction/table-certificate regeneration, manifests, proof holes, authored
axioms, debug declarations, baselines, read-only drift, and the LaTeX build.
It completed with:

```text
PASS baseline verification
PASS LaTeX research notes build
PASS read-only roots unchanged after verification
RESULT PASS authored-targets=57 cache=-no-eco
```

Detailed command results are recorded under `logs/`.

## Week 12 single obligation

Prove actual `RansDecodeTarget.M._rans_decode` consumes the copied Week 11
trace in forward order, selects the original symbols through the concrete
mode-2 tables, finishes in state `2^23`, consumes exactly `size`, and frames
unused output. Do not widen to full HBZ until that generated decoder theorem
fresh-compiles.
