# Follow-up: concrete ordered class-trace P8 evaluator

## Result

`PROVED-CONCRETE-EVALUATOR`

The formerly abstract predicate `P8_bad : int list list -> bool` is now fixed
to the existing five-slot upper-prefix component-cap calculation.  The new
evaluator consumes the full ordered `2 x 256` class trace; it does not replace
the trace by a histogram.

For a well-formed trace with positive `s2` residual headrooms, the evaluator
is the exact nested sum of the existing certified real and imaginary P8
profile bounds divided by the corresponding eighth-power headrooms, together
with the existing trace-independent `s1` terms.  A malformed trace or a trace
with any nonpositive residual headroom is conservatively assigned bound `1`.

The concrete event is

```text
ordered_class_trace_p8_bad(trace) := 1/2 <= trace_p8_union_bound(trace).
```

## Formal surface

`Mode2FaithfulSecurityOrderedClassTraceP8EvaluatorPostFreeze.ec` adds:

- `ordered_class_trace_row`, the list-to-row-function bridge;
- certified trace-dependent real/imaginary profile and bias intervals;
- trace-dependent `s2` headrooms and Markov-8 terms;
- `ordered_class_trace_component_markov8_sum` for the complete five-slot,
  256-root union;
- `ordered_class_trace_p8_admissible`, `trace_p8_union_bound`, and
  `ordered_class_trace_p8_bad`;
- conservative badness for every non-admissible trace;
- a structural certificate connecting the two frozen zero-seed row lists to
  the existing function-valued zero-seed trace;
- exact specialization of the generic sum to the existing zero-seed sum and
  the resulting zero-seed `not P8_bad` theorem under the checked structural
  and numerical certificates; and
- `sampled_dseed_first_attempt_accepted_ordered_class_trace_p8_pr_le_certificate`,
  which instantiates the previous distribution bridge with this concrete
  predicate.

## Executable regression

`check-mode2-ordered-class-trace-p8-evaluator.py` reuses the existing exact
`Fraction`-based upper-prefix evaluator and checks:

- frozen zero-seed trace hash
  `f7f6836125cbc9eec3a1c165f4ff1523a533960677a0908c31278d581707e948`;
- zero-seed bound
  `0.40600526073039882119371744589098288717499145267856 < 1/2`;
- first accepted first-attempt seed index `27`, score `533485`, trace hash
  `ee68332469edc195b37a4b26015f5b7bcd2edf4d0254e89e5e5a9b2b4b6a2d5b`;
- seed-27 bound
  `0.36118553610112440682779752758327045173735490715089 < 1/2`; and
- a one-position rotation of both zero-seed rows preserves their class
  histograms but changes the exact evaluator output.

The full seed-27 ordered trace and its exact rational-sum hash are pinned in
`mode2-first-attempt-seed27-ordered-class-trace-p8.json`.  Its trace hash is
cross-checked against the independently replayed first-attempt feasibility
artifact.

## Boundary

The two numerical results are deterministic evaluator regressions.  They do
not establish:

- an ideal or actual probability mass for `P8_bad` traces;
- a uniform bound for all accepted first-attempt traces;
- context/secret independence;
- a conditional probability given acceptance;
- a SHAKE/XOF idealization or numeric `delta_xof`;
- a direct accumulator-failure probability from trace classification; or
- unbounded retry termination.

## Next research obligation

The predicate is no longer abstract.  The remaining quantitative obligation
is now exactly

```text
mu ideal_summary
  (accepted and ordered_class_trace_p8_bad(trace)) <= epsilon_p8.
```

Discharging it requires an ideal accepted-context distribution or an
equivalent support-and-weight theorem.  Only after a positive acceptance-mass
lower bound is also available may this unconditional mass be divided to form
a conditional probability.
