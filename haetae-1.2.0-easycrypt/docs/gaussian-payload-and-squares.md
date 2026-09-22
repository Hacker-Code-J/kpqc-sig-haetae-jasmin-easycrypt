# Accepted payloads and the Hyperball square sum

Verification status: PASS.

This stage identifies the joint distribution of the visible unsigned sample
vector and the integer square accumulator in one Gaussian batch of a Hyperball
attempt. The input source explicitly draws independent uniform bytes. The
buffer calls reuse the actual sign-copy, carry and finite-consumer procedures;
this is not a distribution claim about a concrete SHAKE seed.

## What one payload records

For a 26-byte candidate, the existing `sigma76_spec` returns a rounded sample,
two raw-square limbs and an acceptance flag. Write

```
m = uint(sample)
q = uint(square_low) + 2^48 * uint(square_high)
payload = m + 2^64 * q
```

`gpd_pack_magnitude` and `gpd_pack_square` prove that division and remainder
recover both integers exactly. The raw square `q` is the value returned by
the candidate computation. It is not the square of the rounded output `m`.
Each actual candidate satisfies `0 <= q <= 2^84 - 1`.

`gpd_accepted` is the distribution obtained by drawing 26 independent uniform
bytes, computing this actual payload and acceptance flag, conditioning on
acceptance, and projecting the payload. Its total mass is one; acceptance
probability is at least `1/7`.

## Keeping the complete accepted history

`GaussianPayloadBuffer.sample` adds a proof-only history to the existing iid
buffer. Under `gib_bounds`, erasing the history preserves its complete returned
triple of sample, sign and square arrays within this explicit iid model. The history records only accepted candidates needed
to finish the request, including the final dummy when the request is 257.

The history-only projection has exactly the distribution
`dlist gpd_accepted n` for `0 <= n <= 512`, with probability-one termination.
The proof handles the actual initial 6,664 bytes, 32-byte sign prefix,
26-byte candidate boundaries, and subsequent 136-byte refills. Already
observed carry bytes remain fixed while averaging over each new block.

## One full Hyperball Gaussian batch

The batch starts with a zero square accumulator and calls `GaussianIidBuffer`
with requests `257, 257, 256, ...`, sample offsets `256*i`, and sign offsets
`32*i`. Its `hip_initial` also sets the sample and sign arrays to zero. These
two initializations are choices of the proof model: production
[`sign.jazz`](../../haetae-1.2.0-jasmin/jasmin/sign.jazz) initializes only `sqsum`
(at lines 1201–1202), leaving the sample/sign stack arrays uninitialized.
The call schedule, offsets, active visible outputs and square accumulation
follow the production Gaussian calls. This is not a whole-state equivalence
to production initialization or a seeded Hyperball execution. Ghost erasure
preserves the whole returned triple between the two explicit iid models.

For the three supported modes:

| Mode | Stored magnitudes | Full accepted history D |
| --- | ---: | ---: |
| 2 | 1,536 | 1,538 |
| 3 | 2,304 | 2,306 |
| 5 | 2,816 | 2,818 |

For a full history `H`, `hip_projection H` returns:

1. The magnitudes after removing zero-based positions 256 and 513.
2. The sum of raw squares from **all D payloads**, including those two positions.

The proved joint law, `hips_actual_joint_law`, is the pushforward
`dmap (dlist gpd_accepted D) hip_projection`. Both observations are computed
from the **same history**. No independence between the vector and its square
sum is assumed or claimed.

The accumulator proof maintains a cumulative accepted-count bound across
calls. The exact inequality `2818 * (2^84 - 1) < 2^96` supplies the headroom
needed for canonical limbs and ordinary integer addition. Starting from
a zero square accumulator discharges the initial-value assumptions; there is no assumed output
fit or assumed distribution of the square accumulator.

<!-- gaussian-payload:contracts:start -->
## Checked public contracts

| Contract | Exact observation and scope |
| --- | --- |
| `gpe_history_law` | For `0 <= n <= 512`, the full accepted history has law `dlist gpd_accepted n`. |
| `gpd_buffer_draw` | For `0 <= n <= 512`, the ghost buffer's history projection is equivalent to drawing that iid payload list; input arrays are unrestricted. |
| `gpt_buffer_correct`, `gpt_buffer_total` | Under `gib_bounds` (request 256/257 and valid offsets), the preceding cumulative-square budget and a total accepted count at most 2818, the complete buffer preserves the history/visible/square invariant; the total contract includes termination. |
| `hip_batch_history_law`, `hip_payload_observe_total` | For modes 2, 3 and 5, the complete history is an iid list of length D, and the returned active magnitudes and canonical integer S equal `hip_projection` of that same history. |
| `hips_actual_joint_law` | Every joint event of the active unsigned vector and S has exactly its probability under `dmap (dlist gpd_accepted D) hip_projection`. |
| `hips_actual_square_law` | Every event of the actual integer accumulator has exactly the probability of `gpd_sum` applied to that list. |
| `hips_actual_safe_probability` | The actual `hbs_good` event has exactly the mass of histories with `3*D*2^74 <= gpd_sum H <= 5*D*2^74`. |
| `hips_actual_terminates` | The explicit iid Gaussian batch terminates with probability one for each supported mode. |

The four `hips_actual_*` contracts require only the supported-mode predicate.
They derive the accumulator representation from the batch; they do not take
a desired square law, output fit, tail estimate or canonical output as a premise.
The public experiment is `HyperballIidGaussian.sample`, a composition of actual
Gaussian helper calls with explicit uniform bytes, not the complete seeded
Hyperball procedure. Its visible-vector law does not include a new signed
or scaled Hyperball output-distribution claim.
<!-- gaussian-payload:contracts:end -->

## Connection to the safe input interval

The earlier [safe-domain proof](hyperball-safe-domain.md) uses
`3*D*2^74 <= S <= 5*D*2^74` and a canonical low limb. Here the accumulator
representation is derived from the actual batch, and its distribution is
the sum of the D accepted raw-square payloads. This provides an exact
probability expression for the interval event.

This stage does not give a numerical upper bound on the probability of
leaving the interval. It does not establish an ideal Gaussian or chi-square
law for these raw squares, an unsafe-acceptance bound, outer Hyperball retry
termination, concrete SHAKE pseudorandomness, or complete API correctness.
Those obligations require additional proofs.

Production code, reference sources, archived proofs and previous proof
sources are unchanged. The new controller and payload encoding are proof
artifacts; they are not new runtime storage or a new input guard.

<!-- gaussian-payload:verification:start -->
## Verification evidence

All 12 new sources passed the final fresh main-target gate, together with
the 168 unchanged non-NTT sources: **180/180 PASS** with `-no-eco`,
explicit `Proofs:check` and the EOF completion guard. Final inventory and
source hashes matched. The full local inventory contains 192 files;
the other 12 NTT targets retain their prior checks and unchanged hashes
and were not rerun in this stage. The gate timestamp is `20260922T054034.419769Z`.

The 484 pinned old sources, including all 180 previous local theory/proof
files, remain unchanged. All 18 gate regressions passed, and the provenance
gate confirmed 102 fresh extraction matches. Production code is unchanged;
KAT was not rerun. No new project axiom or numerical oracle was added.
See [verification evidence](../manifests/verification-results.json),
[source correspondence](../manifests/specification-sources.json) and the
[complete target inventory](../manifests/proof-targets.txt).

Frozen sources added in this stage:

- [GaussianPayloadBufferPath](../proofs/GaussianPayloadBufferPath.ec)
- [GaussianPayloadBufferTrace](../proofs/GaussianPayloadBufferTrace.ec)
- [GaussianPayloadDraw](../proofs/GaussianPayloadDraw.ec)
- [GaussianPayloadEncoding](../proofs/GaussianPayloadEncoding.ec)
- [GaussianPayloadEventLaw](../proofs/GaussianPayloadEventLaw.ec)
- [GaussianPayloadKernel](../proofs/GaussianPayloadKernel.ec)
- [GaussianPayloadTrace](../proofs/GaussianPayloadTrace.ec)
- [HyperballIidPayloadBatch](../proofs/HyperballIidPayloadBatch.ec)
- [HyperballIidSquareLaw](../proofs/HyperballIidSquareLaw.ec)
- [GaussianPayloadBufferSpec](../theories/GaussianPayloadBufferSpec.ec)
- [GaussianPayloadSpec](../theories/GaussianPayloadSpec.ec)
- [HyperballIidPayloadSpec](../theories/HyperballIidPayloadSpec.ec)
<!-- gaussian-payload:verification:end -->
