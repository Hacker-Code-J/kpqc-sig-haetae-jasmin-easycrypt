# Follow-up: sampled first-attempt class-trace joint carrier

## Result

`Mode2FaithfulSecuritySampledFirstAttemptClassTracePostFreeze.ec` closes the
first bridge requested by the accepted-context feasibility audit.  It exposes
the actual sampled-`dseed` first attempt as the ordered observation

```text
(accepted, singular score, 2-by-256 ordered class trace).
```

The trace is derived from the snapshot's correlated `pre_bp` and `avec`
arrays.  It is never replaced by a histogram.

## Checked interfaces

- `first_attempt_row_class_trace` and
  `first_attempt_ordered_class_trace` preserve row and coefficient order.
- `ordered_class_trace_wf` fixes the shape to two rows of 256 entries and the
  class range to `0..5`.
- `first_attempt_class_trace_observation_guard` reuses checked snapshot facts
  to prove `accepted <=> score <= 611098` for the observed tuple.
- `first_attempt_class_trace_joint_distribution` is the exact `dmap` of an
  arbitrary first-attempt trace distribution.
- `sampled_dseed_first_attempt_class_trace_prE` proves event equality between
  the new observation program and the existing sampled-`dseed` first-attempt
  program.
- `sampled_dseed_first_attempt_accepted_class_trace_prE` exposes the exact
  paper-facing event

  ```text
  Pr[accepted and P(ordered trace)].
  ```

- `first_attempt_joint_class_trace_distribution_factor` factors the summary
  through the existing correlated
  `((pre_bp, avec), (s1, sampled_s2))` joint carrier.
- `checked_first_attempt_class_trace_joint_distribution_factor` connects the
  directly observed summary and joint-derived summary under a support-wise
  checked-snapshot witness.  The witness remains explicit.
- `ideal_mode2_joint_event_gap_class_trace_data_processing` transports the
  existing all-event `delta_xof` gap through the summary map without assuming
  independence or conditioning on acceptance.

## Boundary

This result does not condition a distribution on acceptance and does not
establish a probability mass for any trace.  It adds no fixed seed,
context/secret independence, histogram symmetry, SHAKE/XOF idealization,
numeric P8 bound, or retry-termination statement.

In particular, the existence of the joint carrier does not imply that
acceptance restricts the class trace to a small set.  It only makes that joint
question expressible without discarding correlations.

## Completed follow-up and remaining obligation

`Mode2FaithfulSecuritySampledFirstAttemptAcceptedClassTraceP8PostFreeze.ec`
now states the distribution-weighted accepted-trace P8 certificate interface
and composes it with the data-processing path.  Its target is the explicit
bound

```text
Pr[accepted and P8_bad(ordered trace)]
```

over the sampled-`dseed` program, with conclusion
`epsilon_p8 + delta_xof` from an ideal-summary mass certificate at
`epsilon_p8`.

`Mode2FaithfulSecurityOrderedClassTraceP8EvaluatorPostFreeze.ec` now supplies
the concrete order-sensitive `P8_bad` predicate and checks its deterministic
zero-seed and seed-27 diagnostics.  The remaining obligation is solely to
certify the ideal accepted-trace mass of that event numerically.  Conditioning
or division by the acceptance mass remains postponed until a positive lower
bound on that mass is available.
