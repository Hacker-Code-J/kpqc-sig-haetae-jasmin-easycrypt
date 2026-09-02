# Follow-up: accepted-context accumulator feasibility

## Verdict

`UNDER_SPECIFIED_ACCEPTED_CONTEXT_DOMAIN`

The repository does not yet provide a sound optimization domain for an
arbitrary accepted first-attempt class trace.  Acceptance is proved equivalent
to the singular score bound `score <= 611098` and yields a trace-local valid
finalization context.  The useful S2 P8 theorems still require, independently,
that both ordered row traces equal the fixed zero-seed attempt-2 trace.

This is a proof-interface limitation, not evidence that the accumulator is
unsafe and not a proof that every accepted-context analysis is impossible.

## Checked findings

1. `Mode2FaithfulSecurityAcceptedContextClassTraceFeasibilityPostFreeze.ec`
   proves that scalar context validity alone admits every class 0 through 5.
   It deliberately does not claim those witnesses are reachable from an
   accepted KeyGen execution.
2. Histograms are not an exact replacement for the ordered trace.  Both the
   bias and P8 recurrences are root-weighted and contain signed odd moments,
   so permuting equal histogram entries can change the bound.
3. The deterministic seed-index family encodes an unsigned 64-bit index
   little-endian in the first eight bytes of the raw 32-byte seed.  Indices
   0 through 26 reject on their first attempt.  Index 27 is the first accepted
   fixture, with score 533485 and retry counter interval `[0,5]`.
4. Reapplying the current exact caps `(50,65)` to the full ordered index-27
   trace gives:

   - S1 component union: `0.21510396654388705494449682704654388739...`
   - S2 component union: `0.14608156955723735188330070053672656435...`
   - combined union: `0.36118553610112440682779752758327045174... < 1/2`

   Thus this first fixture is not a counterexample to the current fixed-cap
   certificate.  One fixture cannot establish a uniform accepted-context
   theorem.

The exact hashes, trace histograms, seed material, scores, budgets, and claim
boundary are recorded in
`post-freeze/mode2-first-attempt-accepted-context-feasibility.json` and replayed
by `post-freeze/check-mode2-first-attempt-accepted-context-feasibility.py`.

## Next research obligation

Before attempting another global P8 optimization, prove one of the following:

1. **Support route:** an EasyCrypt theorem mapping every accepted first-attempt
   snapshot to an admissible set of full ordered row class traces; or
2. **Distribution route:** a joint law for the accepted class trace and the
   variables used by the singular score, followed by a distribution-weighted
   class-sensitive P8 theorem.

The distribution route is the recommended direction.  The score is computed
from `s1` and finalized `s2`, whereas the class trace is computed from
`pre_bp` and `avec`; treating the score threshold as a direct histogram or
per-class constraint would be unsound without a new joint theorem.

## Non-claims

- no actual accumulator failure lower bound;
- no proof that the current caps work for all accepted contexts;
- no proof that a uniform accepted-context certificate is impossible;
- no accepted class-trace distribution;
- no XOF/RO coupling or unbounded retry theorem.
