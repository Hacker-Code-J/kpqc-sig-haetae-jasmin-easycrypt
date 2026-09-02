# Follow-up: distribution-weighted accepted class-trace P8 bridge

## Result

`PROVED-CONDITIONAL-BRIDGE`

The sampled first-attempt observation can now be instantiated with an
arbitrary order-sensitive trace predicate `P8_bad`.  If an ideal joint law
assigns at most `epsilon_p8` mass to

```text
accepted and P8_bad(ordered 2 x 256 class trace),
```

then the same event for the sampled-`dseed` first-attempt program has
probability at most `epsilon_p8 + delta_xof`, under the existing all-event
joint-gap premise.

## Formal surface

`Mode2FaithfulSecuritySampledFirstAttemptAcceptedClassTraceP8PostFreeze.ec`
adds:

- `accepted_class_trace_p8_bad`, the explicit accepted-and-`P8_bad` event on
  the existing
  `(accepted, score, ordered trace)` observation;
- `ideal_mode2_joint_accepted_class_trace_p8_mass`, the exact event mass on
  the ideal joint summary distribution;
- `ideal_mode2_joint_accepted_class_trace_p8_probability_certificate`, an
  ideal mass certificate with `0 <= epsilon_p8 <= 1`;
- `sampled_dseed_first_attempt_accepted_class_trace_p8_joint_prE`, an exact
  sampled-`dseed` direct/joint observation bridge justified by the checked
  first-attempt snapshot rather than by independence; and
- `sampled_dseed_first_attempt_accepted_class_trace_p8_pr_le_certificate`, the
  final program-level `epsilon_p8 + delta_xof` transport theorem.

The predicate remains a function of the full ordered trace.  No histogram or
per-class count is substituted for the root-weighted signed recurrence.

## Why there is no numeric epsilon yet

The repository has exact trace-dependent P8 machinery and several numerical
certificates for fixed traces.  It does not yet characterize the probability
mass of accepted ordered traces under an ideal joint KeyGen law.  In
particular, the existing joint contract constrains the secret marginal but
does not make the finalize context independent of that secret.

Consequently, none of the existing fixed zero-seed or homogeneous-class
certificates supplies a sound numerical value for `epsilon_p8`.  The bridge
therefore makes the missing quantitative input explicit instead of silently
promoting a fixture or assuming a conditional law.

## Boundary

This result does not establish:

- a numeric accepted-trace P8 mass;
- a SHAKE/XOF idealization or a value for `delta_xof`;
- context/secret independence;
- a conditional probability given acceptance;
- a uniform accepted-context P8 certificate;
- an accumulator failure bound obtained merely from trace classification; or
- unbounded retry termination.

## Next research obligation

Define `P8_bad` from the existing ordered root-interval recurrence, then
construct a checked ideal-summary mass certificate (JSON plus checker and its
EasyCrypt wrapper) for

```text
mu ideal_summary (accepted and P8_bad(trace)) <= epsilon_p8.
```

This requires an ideal accepted-context distribution or an equivalent
support-and-weight theorem.  A finite seed-family experiment may guide the
choice of predicate, but it is not a replacement for that distribution law.
