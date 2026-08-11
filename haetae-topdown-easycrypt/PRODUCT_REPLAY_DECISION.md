# Week 7 product/replay decision

Date: 2026-08-07

## Decision

- `OBL-MU-PRODUCT-REPLAY`: `DEFERRED` / explicit paper boundary
- research boundary: `EXPLICIT PAPER BOUNDARY`
- `OBL-DIRECT-OBSERVED-MU`: stays `PARTIAL`
- `delta_mu_raw_api_accept = 0`: not claimed

## Time-boxed target

The Week 7 prototype was allowed to succeed only if both of the following were
compiled:

1. the actual generated procedures
   `SignMuHashTarget.M._sf_mu_rawpre` and
   `VerifyMuHashTarget.M.__verify_hash_mu`
   appeared directly in the theorem surface; and
2. the replay/product return values were proved equal to the values stored in
   `SignRawApiMuTrace.observed_mu` and
   `VerifyCryptolabMuTrace.observed_mu`, not merely to a fresh replay witness.

## What is already compiled

- `RegionLocalMuTop.sign_verify_generated_raw_mu_prefix_regionwise`
  proves the actual generated Sign/Verify raw hash relation on the returned
  values of `SignMuHashTarget.M._sf_mu_rawpre` and
  `VerifyMuHashTarget.M.__verify_hash_mu`.
- `RawApiDirectObservedMu.raw_sign_then_verify_actual_exact_trace`
  proves exact actual-to-trace control/result/final-memory preservation for
  the sequential raw Sign then cryptolab Verify execution.
- `RawApiVerifyAcceptTrace.verify_cryptolab_actual_accept_implies_trace_tail_reached`
  and the accepted-input binding theorems prove the accepted Verify trace
  reaches the real `__verify_hash_mu` call and expose its hash inputs.

## Blocking semantic gap

The missing bridge is not another byte-locality lemma.

The open step is:

```text
generated returned-hash-value pRHL theorem
  =>
stored post-state observation equality
```

for two hash calls that occur inside two already completed sequential traces
with different residual continuations:

- Sign residual continuation:
  `_sf_signature_core_mode2` after `_sf_mu_rawpre`
- Verify residual continuation:
  `__verify_challenge_m23 ; _poly_mismatch` after `__verify_hash_mu`

Without a justified product/replay rule, the project cannot transport the
compiled generated-hash equality theorem to:

```text
verify_result = W64.zero =>
mu32_prefix(
  SignRawApiMuTrace.observed_mu,
  VerifyCryptolabMuTrace.observed_mu)
```

The bounded EasyCrypt proof state has incompatible surfaces:

```text
pRHL context:
  res{1} = return(_sf_mu_rawpre) /\
  res{2} = return(__verify_hash_mu)
  ==> mu32_prefix(res{1}, res{2})

sequential unary post-state:
  SignRawApiMuTrace.observed_mu
  VerifyCryptolabMuTrace.observed_mu
  VerifyCryptolabMuTrace.tail_reached
```

After the two trace calls have returned, the hash-call return variables no
longer occur in the unary goal. Conversely, applying the pRHL theorem at the
hash-call point leaves the unequal Sign and Verify residual continuations.
EasyCrypt's one-sided sequencing cannot discard the Sign continuation without
the missing losslessness fact. Thus `sim`, `seq`, and direct consequence do
not provide the required bridge; the obstacle is not a failed SMT arithmetic
side condition.

## Rejected approaches

- add another caller or observation wrapper:
  rejected by Week 7 scope and by the requirement to stop widening wrappers
- assume observation equality as a precondition:
  invalid, because it would restate the goal
- introduce a SHAKE locality axiom:
  forbidden by the sprint policy
- discard the unmatched Sign continuation:
  unjustified without the still-open Sign losslessness/termination obligations

## Consequence for the paper boundary

The current compiled security-facing boundary is:

- accepted raw Verify control and actual hash-input binding;
- actual generated Sign/Verify raw hash-call equality; and
- actual generated position-64 challenge-suffix helper equality.

The uncompiled edge is exactly the direct post-state equality between the two
trace modules' stored `observed_mu` fields.

This is a semantic gap, not an extraction gap. The actual generated hash
procedures are already present in the theorem surface, but the proof does not
yet contain a unary transport rule from returned hash results to stored trace
observations, and the current traces do not preserve a hash-time memory
snapshot that would make that transport trivial. A one-sided elimination of the
unmatched Sign continuation would also require the still-open Sign
losslessness/termination story, so the sprint correctly stops here.

Week 8 should not reopen this lane by stacking more wrappers. The correct next
main lane is signature codec functional correctness.
