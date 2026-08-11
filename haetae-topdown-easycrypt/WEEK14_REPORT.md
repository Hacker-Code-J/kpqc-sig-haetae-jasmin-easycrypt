# Week 14 report - production full HBZ wrapper boundary

Date: 2026-08-10

## Decision

**GO-HBZ.** `OBL-SIG-HBZ-ENCODE-DECODE` is now **PROVED (success-conditioned
partial correctness)** at the production wrapper boundary. The exact source
theorem is `Mode2HbzSignatureBoundaryLift.signature_pack_unpack_hbz_full_actual_exact`.
Its Hoare corollary is `signature_pack_unpack_hbz_full_inverse_mode2`.

This note documents the production wrapper surface, not a termination claim.
Encoder success reachability and the all-zero witness remain separate.

## Production theorem surface

The boundary-lift file ties together the production SignaturePack/Unpack route
and the focused full-HBZ wrapper route. It reuses the lower-level theorem
surface from:

- `Mode2HbzInternalBoundaries.full_encode_prepare_mode2_correct`
- `Mode2HbzFullEncodeTrace.actual_encode_hb_z1_full_mode2_trace`
- `Mode2HbzFullDecodeInverse.actual_decode_hb_z1_full_mode2_inverse`
- `Mode2HbzFullActualInverse.actual_hbz_full_encode_decode_inverse_mode2`

The exact theorem
`signature_pack_unpack_hbz_full_actual_exact` proves that the production
SignaturePack/Unpack harness and the focused full-HBZ harness expose the same
result tuple and the same `decoder_ran` flag. The public Hoare corollary
`signature_pack_unpack_hbz_full_inverse_mode2` then states the exact same
success/failure disjunction over the pack/unpack harness.

## Direct call surfaces

The production boundary keeps two direct call surfaces explicit:

```text
SignaturePackUnpackHbzFullHarness.run
  -> SignaturePackMode2Target.M._encode_hb_z1_full
  -> SignatureUnpackMode2Target.M._decode_hb_z1_full

HbzFullActualHarness.run
  -> HbzFullEncodeTarget.M._encode_hb_z1_full
  -> HbzFullDecodeTarget.M._decode_hb_z1_full
```

The exact theorem shows those two harnesses are aligned on both the returned
buffers and the decoder-reachability flag.

## Compiled theorem contracts

- `Mode2HbzFullEncodeTrace.actual_encode_hb_z1_full_mode2_trace`
  (`easycrypt/refinement/sign/Mode2HbzFullEncodeTrace.ec:27`) targets the
  actual focused full encoder.  Its precondition binds the initial output and
  HBZ arrays, the literal mode-2 encoder table, `(count,mhb,offset) =
  (1024,13,6)`, and `canonical_hbz_mode2 hbz0`.  Its postcondition preserves
  both the zero-size failure result and the nonzero-size result with the
  actual prepare-local `prepared_symbols`, exact trace size/segment, and
  encoded tail frame.
- `Mode2HbzFullDecodeInverse.actual_decode_hb_z1_full_mode2_inverse`
  (`easycrypt/refinement/sign/Mode2HbzFullDecodeInverse.ec:31`) targets the
  actual focused full decoder.  It assumes the literal decoder tables,
  `(1024,13,6)`, canonical original coefficients, the prepared-symbol
  relation, exact trace size/bounds/segment, and exact initial bindings.  It
  concludes decoder `bad = 0`, the original 1024-coefficient prefix, and the
  coefficient tail frame.  Decoder success and apply execution are not
  premises.
- `Mode2HbzFullActualInverse.actual_hbz_full_encode_decode_inverse_mode2`
  (`easycrypt/refinement/sign/Mode2HbzFullActualInverse.ec:68`) targets the
  direct focused harness.  Its entire semantic precondition is exact harness
  argument binding plus `canonical_hbz_mode2 hbz0`; in particular it has no
  encoder-success, `size > 0`, trace, prepared-symbol, decoder-success, or
  decoded-equality premise.  Its postcondition is the failure/success
  disjunction below.
- `Mode2HbzSignatureBoundaryLift.signature_pack_unpack_hbz_full_actual_exact`
  and `signature_pack_unpack_hbz_full_inverse_mode2`
  (`easycrypt/refinement/sign/Mode2HbzSignatureBoundaryLift.ec:67` and `:92`)
  lift the same contract to the actual `SignaturePackMode2Target` /
  `SignatureUnpackMode2Target` procedures through compiled exact
  equivalence.

## Branches

The production theorem keeps the encoder result branch explicit.

### Failure branch

- `size = 0`
- `decoder_ran = false`
- `encoded = out0`
- `decoded = decoded0`
- `bad = bad0`

The decoder is skipped, and the initialized outputs are retained.
Canonical prepare correctness forces the actual prepare result's bad word to
zero and supplies the prepared-symbol witness.  Consequently the prepare
failure branch is discharged as unreachable under this precondition; the
retained `size = 0` result is the actual rANS-encoder failure branch.  This
does not claim that the failure branch itself is unreachable.

### Success branch

- `size <> 0`
- `4 <= size <= 1024`
- `decoder_ran = true`
- `bad = 0`
- `decoded_hbz_prefix`
- `coeff_tail_frame`
- `suffix_frame`
- an explicit `prepared_symbols` witness
- `segment_matches` against `mode2_trace_bytes(prepared_symbols)`

The success branch is still success-conditioned partial correctness. It proves
the production wrapper composition, not success reachability.

## Open edge

The only remaining HBZ-specific open edge is the actual all-zero success
witness. That witness stays `PARTIAL`, so the unconditional round-trip claim
is still not total. The `h` codec remains out of scope.

## Week 15 recommendation

Focus on the actual success witness only. Do not widen to the `h` codec until
the witness compiles.

## Verification note

`scripts/verify-all.sh` passed on 2026-08-10 with
`RESULT PASS authored-targets=72 cache=-no-eco`.  The run also passed the
Week 14 source-surface checks, focused extraction regeneration and hash drift,
internal procedure identity, deterministic HBZ table certificate, selected
upstream baselines, proof-hole/authored-axiom/debug scans, read-only-root
checks, and the LaTeX build.  The aggregate result is recorded in
`logs/verify-all-summary.txt`.
