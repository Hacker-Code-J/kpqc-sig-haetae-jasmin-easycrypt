# Week 13 independent verifier audit

## Verdict

**PASS.** `OBL-RANS-CORE-INVERSE` is supported as
success-conditioned Hoare partial correctness.

## Evidence

- `Mode2RansCoreActualInverse.ec:35-76`: the final theorem's precondition is
  only exact argument binding plus `mode2_hbz_symbol_stream`. The failure and
  success postconditions are both explicit.
- `Mode2RansActualInverse.ec:46-79`: the existing harness directly calls
  actual `_rans_encode`, actual `__copy_encoded_suffix`, and actual
  `_rans_decode`.
- `Mode2RansCoreCompositionBridge.ec:81-215`: copied trace equality and every
  decoder pointwise byte-read premise are derived from `segment_matches` and
  the actual copy slice; they are not harness assumptions.
- `Mode2RansCoreCompositionBridge.ec:218-253`: W64 subtraction is related to
  integer trace size under the actual success bounds, with unsigned no-wrap.
- `Mode2RansCoreActualInverse.ec:95-247`: the proof sequentially invokes the
  existing actual encoder, copy, and decoder theorems and constructs the
  decoder input predicate from their post-state.
- `logs/verify-all-summary.txt:98`: clean authoritative result is
  `RESULT PASS authored-targets=67 cache=-no-eco`.

## Boundary audit

- Encoder success is not a precondition.
- Decoder success, copied-trace equality, decoder read equality, and decoded
  equality are not preconditions.
- Success post includes decoder `bad=0`, `off=encoded_size`, recovery of 1024
  symbols, and the decoded tail frame.
- Failure post includes `decoder_ran=false` and preservation of initial
  decoded/state values.
- Documentation does not promote the theorem to success reachability,
  termination/losslessness, production full-HBZ wrapper correctness,
  canonical parsing, encoding zero-loss, or implementation security.

## Remaining risks

- `OBL-RANS-ACTUAL-SUCCESS-WITNESS` remains `PARTIAL`.
- `OBL-SIG-HBZ-ENCODE-DECODE` remains `PARTIAL`.
- Encoder/decoder termination and the production full-HBZ wrapper composition
  remain unproved.
