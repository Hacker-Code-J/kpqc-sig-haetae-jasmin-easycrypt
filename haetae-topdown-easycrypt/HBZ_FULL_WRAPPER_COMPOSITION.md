# Mode-2 full HBZ wrapper composition

## Scope

This note records the production full-wrapper boundary for the mode-2 HBZ
lane. The direct wrapper path is:

```text
HbzFullActualHarness.run
  -> HbzFullEncodeTarget.M._encode_hb_z1_full
  -> HbzFullDecodeTarget.M._decode_hb_z1_full
```

The exact production theorem is
`Mode2HbzSignatureBoundaryLift.signature_pack_unpack_hbz_full_actual_exact`.
The Hoare corollary is `signature_pack_unpack_hbz_full_inverse_mode2`.

This is success-conditioned partial correctness. It is not a termination
theorem and it does not prove that the success branch is reachable for every
canonical input.

## Exact theorem surface

The production lift is built on four compiled edges:

- `Mode2HbzInternalBoundaries.full_encode_prepare_mode2_correct`
- `Mode2HbzFullEncodeTrace.actual_encode_hb_z1_full_mode2_trace`
- `Mode2HbzFullDecodeInverse.actual_decode_hb_z1_full_mode2_inverse`
- `Mode2HbzFullActualInverse.actual_hbz_full_encode_decode_inverse_mode2`

The exact theorem
`signature_pack_unpack_hbz_full_actual_exact` proves that the production
SignaturePack/Unpack harness and the focused full-HBZ harness return the same
result tuple and the same `decoder_ran` flag. The Hoare corollary then keeps
the encoder-size branch explicit.

## Failure branch

When the encoder returns `size = 0`:

- the decoder is not run;
- `decoder_ran = false`;
- the initial encoded buffer is preserved;
- the initial decoded buffer is preserved;
- the initial `bad` value is preserved.

This branch is part of the theorem, not a separate assumption.
For canonical input, the compiled prepare theorem yields a zero prepare-bad
word and the actual prepare-local symbol array.  The wrapper proof therefore
eliminates the prepare-failure guard; the remaining zero-size return is the
actual rANS-encoder failure branch.  The theorem still preserves that branch
and does not assert that it is unreachable.

## Success branch

When the encoder returns `size <> 0`:

- `4 <= size <= 1024`;
- `decoder_ran = true`;
- the decoder returns `bad = 0`;
- `decoded_hbz_prefix` holds for the original HBZ input;
- `coeff_tail_frame` holds for the preserved tail;
- `suffix_frame` holds for the encoded buffer;
- there exists a `prepared_symbols` witness;
- `segment_matches` holds against `mode2_trace_bytes(prepared_symbols)`.

This is the production wrapper composition. It is Hoare partial correctness
with an explicit success branch, not a proof that the branch is always
reachable.

## Remaining edge

The remaining open edge is the actual all-zero success witness. Until that is
proved, `OBL-SIG-HBZ-ENCODE-DECODE` should be read as success-conditioned
partial correctness, not as an unconditional round-trip theorem.
