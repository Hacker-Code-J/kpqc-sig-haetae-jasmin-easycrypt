# Week 16 MINCORE-SIGN report

## Decision

**STOP-SIGN-CHAL-MODE2.**

The three requested actual helpers are now regenerated as one focused target
and are called directly, in order, by a transparent authored harness. The
checked theorem proves the acceptance-control fact at that boundary: the hint
call is taken exactly when the actual `_sf_z_check` return is zero. It does not
claim (S-1)--(S-7).

The first Sign-specific semantic leaf needed to continue is absent:

```text
sf_challenge_mode2_highbits_lsb_sampleinball_correct
```

It must prove that the actual `_sf_challenge_mode2` path computes
`HighBits_512(w)`, packs that value and `LSB(floor(y0))` in the specified
order with the first 32 bytes of `mu`, and returns the mode-2
`SampleInBall(...,58)` challenge. No theorem with this contract exists in the
checked tree. The existing transcript work stops at the mu32 absorb seam, and
the current security-model `challenge_hash` ignores its `highbits` argument,
so it cannot be reused as this leaf without changing the target statement.

There is also an independent earlier algebraic dependency for paper-literal
(S-1), and again for (S-4): the already-frozen full-NTT
pointwise-product/negacyclic-convolution theorem. The user-requested scope
forbids reopening KeyGen NTT, so this Sign pass records that dependency but
does not broaden into it. Closing the challenge leaf alone would therefore
not justify GO-SIGN.

## Preserved baseline

Before this pass, the complete aggregate log was copied byte-for-byte to
`logs/verify-all-before-week16-sign.log`. It contains exactly 77
`PASS fresh compile` lines and terminates with

```text
RESULT PASS authored-targets=77 cache=-no-eco
```

Its SHA-256 is
`8480d2e2f2ddda421c3d244ab5ec0a50196cadd7a8e1a29e996fd307aec7db57`.
The new target extends the manifest to 78; it does not replace or weaken any
of the 77 baseline targets.

## Focused actual boundary

`scripts/extract-sign-accepted-core.sh` invokes `jasmin2ec` on exactly these
roots from pinned `haetae-ref-jasmin/jasmin/sign.jazz`:

1. `_sf_round_challenge_mode2`;
2. `_sf_z_check`; and
3. `_sf_hint_mode2`.

The regenerated `SignAcceptedCoreTarget.ec` hash is
`ebfe228473760f2f0978ef262c6a5d1f5ef5d01307b2cc0f7f76623fb4ab4b1d`.
The extraction selects no hyperball sampler, retry loop, packer, codec, or
public API entry point.

`Mode2SignAcceptedCore.ActualSignAcceptedCore.run` calls the three generated
procedures directly. The third call is syntactically and semantically guarded
by the actual `_sf_z_check` result. The checked theorem
`actual_sign_accepted_core_branch_control_mode2` has precondition `true`; it
contains no accepted-result fact, paper equation, norm condition, hint
equation, or final output equality.

This is a partial-correctness control result only. It neither invokes nor
models the sampler, and it makes no distribution or termination claim.

## S-1--S-7 audit

| Item | Actual path | Status and exact missing leaf |
| --- | --- | --- |
| S-1 `w=A floor(y)` | round/copy, forward NTT, matrix pointwise accumulation, inverse NTT | **STOPPED.** Needs the already identified full-NTT convolution/odd-root orthogonality theorem plus the `Rq.poly`-to-paper adapter. This pass does not reopen KeyGen NTT. |
| S-2 `w1=HighBits_512(w)` | `_polyvec_highbits_hint_m23` inside `_sf_challenge_mode2` | **STOPPED.** First half of `sf_challenge_mode2_highbits_lsb_sampleinball_correct`. |
| S-3 challenge equation | highbits pack, LSB pack, `__sign_challenge_m23` | **STOPPED.** Second half of the same exact leaf; current checked abstract `challenge_hash` omits highbits. |
| S-4 `z=y+(-1)^b cs` | challenge products followed by `_sf_add_cs_and_check` | **STOPPED.** The machine loop visibly uses `factor=1-2*(b&1)` and scale 8192, but a checked convolution/representation theorem for both `cs` arrays and an integer-semantics loop invariant are absent. |
| S-5 first norm bound | `stotal1`, subtraction from 6496508945891328, top-bit test | **STOPPED.** Needs `_sf_add_cs_and_check_mode2_integer_semantics`, including signed-W32 interpretation, exact W64 sum/no-wrap, and boundary strictness. |
| S-6 second norm predicate | `stotal2`, subtraction of 6505809026482176, top-bit test gated by `(b&2)>>1` | **STOPPED.** The same leaf must also prove the sampler-byte-to-`b'` encoding and the exact strict comparison; neither is assumed. |
| S-7 hint equation | `_sf_round_lk`, then `_sign_make_hint(...,256,9,252)` | **STOPPED.** Needs `_sf_hint_mode2_hint_equation_correct`, connecting fixed-point rounding/freezing/highbits to the coefficientwise mod-252 equation. |

In particular, source-level expressions are not promoted to theorems. The
response equation, both integer norm predicates, and the hint equation remain
explicit non-claims.

## Forbidden-premise audit

The authored operational theorem does not put any of the following in its
precondition:

- `reject = 0` or successful acceptance;
- (S-1)--(S-7), including the response or hint equations;
- either norm predicate;
- equality of the final returned arrays; or
- sampler distribution, losslessness, or termination.

Valid secret-key and sampler representations remain admissible assumptions
for the future semantic leaves, but this control theorem does not need them.

## Verification evidence

The individual focused extraction and authored target both compile fresh with
`-no-eco`.  The final single-writer aggregate run contains exactly 78
`PASS fresh compile` lines, exactly one terminal result line, and ends with

```text
RESULT PASS authored-targets=78 cache=-no-eco
```

That clean aggregate is preserved as `logs/verify-all-week16-sign.log`; its
SHA-256 is
`cf8056712327dc8211cf93ae427ac5053e8a9d2366747f171392468ac3ff0d75`.
The aggregate also passed source drift, proof-hole, authored-axiom,
debug/temporary-declaration, manifest, generated-extraction drift, LaTeX, and
read-only-root checks.

## Transition

MINCORE-SIGN is frozen at this checked actual-call boundary. In accordance
with the stop rule, the active lane moves to MINCORE-VERIFY. This report does
not claim that the Sign blocker has been solved, and it does not widen into
KeyGen, codecs, packers, public APIs, or full-signature correctness.
