# Week 16 MINCORE-VERIFY report

## Decision

**PARTIAL-VERIFY-MATRIX-CRT.**

The current Verify work opens the canonical decoded \((x,v,h,c)\) boundary and
directly composes the actual helpers in order:

1. `_verify_prepare_z1_wprime`
2. `_verify_matrix_crt`
3. `_sign_verify_recover_w_z2`
4. `_sign_verify_norm_reject`
5. `_sign_verify_tail_m23` under the actual zero-reject branch

The checked work now preserves the exact machine-word/control boundaries for
the requested V-1, V-2, V-5, V-6, the norm gate, and the tail call trace.
It does not prove the paper-level Verify formula package, and it does not
claim `GO-VERIFY`.

## Preserved baseline

Before this pass, the complete aggregate log was copied byte-for-byte to
`logs/verify-all-before-week16-verify.log`. It contains exactly 78
`PASS fresh compile` lines and terminates with

```text
RESULT PASS authored-targets=78 cache=-no-eco
```

Its SHA-256 is
`cf8056712327dc8211cf93ae427ac5053e8a9d2366747f171392468ac3ff0d75`.

The new Verify manifest contains 82 authored targets. Its completed aggregate
log is preserved as `logs/verify-all-week16-verify.log`; it contains exactly
82 `PASS fresh compile` lines, exactly one terminal result line, and ends with

```text
RESULT PASS authored-targets=82 cache=-no-eco
```

Its SHA-256 is
`46e7dac8e442c820f746139a164c8bc00d6af17b7ad25cbd5d195507fddae03c`.

## Focused actual boundary

The focused Verify core is split into four direct, checkable pieces:

- `Mode2VerifyCoreSequence.ActualVerifyCoreSequence.run`
- `Mode2VerifyPrepareNorm`
- `Mode2VerifyRecover`
- `Mode2VerifyTailChallenge`

The sequence harness calls the actual helpers in the exact order above and
stores the intermediate arrays/words so that each leaf can be audited
independently. The harness is control-only: it does not assume reject `= 0`,
does not assume a reconstruction result, does not assume the norm passes, and
does not assume challenge equality.

## Proven subresults

### V-1 and V-2

`Mode2VerifyPrepareNorm.ec` proves exact machine-word semantics for the
boundary helpers that prepare the decoded object:

- `verify_prepare_z1_wprime_mode2_word_exact`
- `verify_prepare_z1_mode2_word_exact`
- `verify_prepare_wprime_mode2_word_exact`

These are word-level prefix/frame theorems for the actual generated
procedure. They establish the exact machine-word accumulator and prefix
relations used by the focused Verify boundary. They do **not** claim the
paper-level integer reconstruction formulas.

### V-5 and V-6

`Mode2VerifyRecover.ec` proves exact machine-word semantics for the recovery
helpers:

- `actual_sign_verify_recover_w_z2_mode2_word_semantics`
- `actual_sign_verify_recover_w_mode2_word_semantics`
- `actual_sign_verify_recover_z2_mode2_word_semantics`

These theorems capture the exact word-level recovery path, including the
recovery of `w` and the `z2` word result. They do **not** prove the paper
bridge for the parity/centering interpretation of V-6, and they do not
assert a semantic integer equality beyond the exact word result.

### Norm gate

`Mode2VerifyPrepareNorm.ec` also proves the exact W64 norm accumulator and
gate:

- `polyvec_sqnorm2_mode2_word_accumulator`
- `sign_verify_norm_reject_mode2_word_exact`

This is the exact machine-word reject gate used by the actual Verify tail
control. It does **not** prove the separate integer no-wrap bridge needed for
the paper norm predicate.

### Tail trace and challenge word expression

`Mode2VerifyTailChallenge.ec` proves the exact tail call trace and the actual
comparison word:

- `verify_tail_exact_trace_mode2`
- `poly_mismatch_mode2_word_exact`

These are the exact generated-procedure boundary facts for the helper trace
and the final mismatch word expression. They do **not** identify the tail
path with the paper highbits/LSB/`mu`/`SampleInBall` challenge semantics.

## Exact blockers

The earliest missing Verify leaf is:

```text
verify_matrix_crt_mode2_fromcrt_freeze_exact
```

That missing leaf blocks the paper-level matrix reconstruction story.
Downstream from it remain:

- the full-NTT convolution / odd-root orthogonality theorem;
- the `Rq.poly`-to-integer-list adapter needed for the security-model
  multiplication statement; and
- the paper-level rewrite from the checked matrix helper to the claimed
  reconstruction formula.

The challenge side still lacks:

```text
verify_tail_m23_highbits_lsb_sampleinball_correct
```

That leaf would have to relate the actual tail highbits/LSB packing and the
actual challenge comparison path to the paper `SampleInBall(...,58)` result.
No such theorem is claimed here.

## Forbidden-premise audit

The checked control theorem does not put any of the following in its
precondition:

- `reject = 0`
- a reconstruction result
- a norm-pass result
- challenge equality
- paper-level `(V-1)`--`(V-6)` formulas
- sampler distribution
- termination

The report also excludes the following scope items:

- parser and malformed-input handling
- codec internals
- public API orchestration
- KeyGen NTT expansion
- Sign blockers

## Verification evidence

The focused `VerifyCoreTarget.ec` regeneration and all four authored Verify
targets individually fresh-compiled with `-no-eco`. The final single-writer
aggregate then fresh-compiled all 82 targets and passed proof-hole,
authored-axiom, debug/temporary, manifest, focused-extraction/hash, direct-call
order, forbidden-premise, scope, selected-baseline, LaTeX, and before/after
source-drift gates. The preserved 78/78 baseline remains unchanged.
