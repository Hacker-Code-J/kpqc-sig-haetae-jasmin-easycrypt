# Gaussian retries, ordered batches and finite input prefixes

This stage connects repeated calls to the extracted Jasmin attempt with its
conditioned output law, then derives the joint law of an ordered batch. The
finite byte-prefix model also supplies an explicit adequacy condition for the
production buffered consumer. The concrete SHAKE consumer also has a checked termination theorem under
that explicit adequate-prefix condition.

Use the independent target from
[Gaussian magnitude identification](gaussian-magnitude-identification.md):

```
Pr[G=k] = exp(-k*k/2^153) / sum_{j in Z} exp(-j*j/2^153)
R       = floor((abs(G)+32768)/65536).
```

Write `A_p = sc_actual_conditioned p` and `J_p = sc_actual_pair p`.
The prior identification proves `SDist(A_p, law(R)) < 2^-39`.

## Operational retry with independent inputs

`GaussianRetryActual.sample(p)` repeatedly invokes
`SigmaJoint203Experiment.sample(p)` until its acceptance flag is true. Every
invocation draws fresh independent uniform inputs of 83, 72 and 48 bits and
calls `SamplerTarget.M.__sample_gauss_sigma76_regs`. The returned value is the
unsigned decoded rounded magnitude from the first accepted attempt.

`gr_actual_pair_law` identifies the whole `(magnitude, accepted)` pair,
including rejected outcomes, with `J_p`. This permits replacement of calls
inside the retry loop. The generic `GaussianRetry.sample(d)` redraws from d;
under losslessness and positive acceptance mass, its law is
`gr_output d = dmap (dcond d gr_accept) fst`.

The established lower bound `mu J_p sc_accepted >= 1/7` closes those premises.
`gr_actual_retry_ll` proves probability-one termination, and for every integer
output event S, `gr_actual_retry_law` gives

```
Pr[GaussianRetryActual.sample(p) returns a value in S] = mu A_p S.
```

`gr_actual_retry_gaussian_event` consequently bounds its event error against
R by `2^-39`. The base template p is unrestricted. These are operational
results for the explicit independent-input wrapper; no randomness assumption
about concrete SHAKE bytes is used.

## Entire ordered batches and the dummy

`GaussianRetryActualBatch.sample(p,n)` calls that retry procedure n times and
appends each accepted magnitude in order. For `n>=0`, `gra_batch_joint_law`
proves, for every event E on integer lists,

```
Pr[GaussianRetryActualBatch.sample(p,n) returns a list in E]
  = mu (dlist A_p n) E.
```

`gra_batch_total` and `gra_batch_size_total` prove termination and exact length
with probability one. For `n>0`, product distance gives

```
SDist(dlist A_p n, dlist law(R) n) < n / 2^39.
```

Thus the full 256-vector has distance below `2^-31`; the full 257-vector has
distance below `257/2^39`. These bounds apply to every event on the whole list.

The 257th accepted sample remains in the mathematical full vector.
`GaussianRetryActualBatch.prefix256` consumes all 257 accepted samples before
returning the first 256. `gra_prefix256_law` proves its exact law is
`dlist A_p 256`, with the same `2^-31` error bound and probability-one
termination. This projection preserves accepted order.

## Finite canonical candidate-byte prefixes

`gr_candidate_distribution p` encodes the same independent 83/72/48-bit inputs
as a 26-byte candidate. Bytes 0 through 10 encode the CDT input, bytes 11
through 16 the rejection input, and bytes 17 through 25 the noise input. The
unused high five bits of byte 10 are zero. This is a canonical 203-bit input
law, not uniform sampling of all 208-bit arrays.

For a finite candidate list, `gr_candidate_stream` concatenates its bytes.
`gr_candidate_stream_events` recovers the exact `sigma76_spec` word tuple for
each complete candidate, retaining magnitude, both square limbs and acceptance.
`gr_candidate_stream_pairs_iid` identifies the pair projection with
`dlist J_p length`; `gr_candidate_stream_accepted_iid` preserves the accepted
subsequence. Values outside the supplied finite prefix are only a convention
for making the byte function total. No distribution over infinite functions
is assumed.

Let failure mean fewer than n accepted events in the supplied prefix. For
integers `n,t>=0`, the prefix of **n*t candidates** satisfies

```
Pr[shortfall after n*t candidates] <= n*(6/7)^t.
```

`grbt_prefix_shortfall` proves this by splitting the independent prefix into n
blocks of t trials: a shortfall implies at least one block has no acceptance.
For one retry the exact no-acceptance probability is `(1-a)^t`, where a is the
acceptance mass. `gr_prefix_failure_bound` transfers the bound to candidate
bytes and the same adequacy predicate used by the buffer proof.

`gr_prefix_failure_limit` proves convergence to zero as the arbitrary finite
prefix length tends to infinity, not only along lengths divisible by n.
`gr_block_prefix_failure_limit` proves the corresponding limit along buffer
block counts. These are limits of finite-prefix probabilities, including
requests 256 and 257.

## Production buffer linkage and conditional totality

The production procedure is
`ApiTarget.M(ApiTarget.Syscall)._sf_sample_gauss_N_full_at`, abbreviated
`StreamSigner._sf_sample_gauss_N_full_at` in the proofs. Its first 32 stream
bytes supply signs. Subsequent bytes form continuous 26-byte candidates across
the initial 49 blocks and later 136-byte refills. After B blocks,

```
gs_stream_attempts B = floor((136*B-32)/26).
```

The initial 49 blocks contain 255 complete candidates and two carried bytes.
Each refill contributes five or six further complete candidates. Carrying the
remainder preserves candidate boundaries.

`gr_adequate f n T` requires `n>=0`, `T>=0` and at least n accepted events among
the first T candidates of f. For the concrete SHAKE state, f is
`fun j => shake_stream_byte (shake_initial_words seed nonce) (32+j)`.
The sufficient block cap is
`gr_block_cap T = max 49 (floor((26*T+167)/136))`.

`gr_sample_gauss_N_prefix_correct` states the Hoare bridge to
`gr_prefix_result` at that exact T. Its input conditions include `n=256` or
`n=257`, a nonnegative sample offset with `offset+n<=4096`, a nonnegative sign
byte offset with `offset+32<=512`, and both initial square limbs below `2^48`.
The result specifies the copied sign bytes, output frame and full accepted
event semantics. Both requests store the first 256 accepted magnitude words. For
257, the dummy slot remains unchanged, while the dummy's two returned square
limbs still contribute to the accumulator:

```
value(final_squares) = value(initial_squares)
                    + sum_selected (uint(square_lo) + 2^48*uint(square_hi)).
```

The selected list has n events. This is the exact sum of the attempt's square
limbs; it does not replace them with the squares of the rounded magnitudes.

`GaussianRetryStreamTermination.gr_sample_gauss_N_prefix_total` proves the
same precondition and `gr_prefix_result` postcondition with probability one.
The proof uses bounded consumer totality and a decreasing finite rank for the
refill loop. Among compatible block indices between 49 and the adequate cap,
it takes the maximum. An unfinished state cannot be compatible with the cap;
the body advances that maximum witness, so the remaining rank decreases.
This does not require different SHAKE blocks to have different internal states.

The independent-input retry/batch law, finite canonical-prefix probabilities
and this conditional concrete-SHAKE theorem are separate statements. This
stage does not establish an independent-input distribution law for the entire
buffered controller, independence of concrete SHAKE outputs, or termination
for every seed. It also does not identify the implementation's later sign
handling, Hyperball distribution or complete signature APIs.

## Proof map and verification status

The stage adds 15 proof files. Each path below is relative to `proofs/`.

| File | Main result or role |
| --- | --- |
| `GaussianRetryCore.ec` | `gr_retry_law`, `gr_retry_total`: generic executable rejection loop and its conditioned law. |
| `GaussianRetryAttempt.ec` | `gr_actual_pair_law`, `gr_actual_pair_equiv`, `gr_actual_acceptance_lower`: actual full-pair law and acceptance at least 1/7. |
| `GaussianRetryActual.ec` | `gr_actual_retry_ll`, `gr_actual_retry_law`, `gr_actual_retry_gaussian`: actual independent-input retry. |
| `GaussianBatchDistance.ec` | `gb_batch_distance`, `gb_batch_256_2m39`, `gb_batch_257_2m39`, `gb_dlist_prefix`: product distance and prefix projection. |
| `GaussianRetryBatch.ec` | `grb_batch_joint_law`, `grb_batch_lossless`, `grb_batch_257_take256_law`: ordered generic retry batches. |
| `GaussianRetryBatchCorrectness.ec` | `gra_batch_joint_law`, `gra_batch_total`, `gra_batch_256_gaussian`, `gra_batch_257_gaussian`, `gra_prefix256_law`: actual wrapper transfer. |
| `GaussianRetryTail.ec` | `gaussian_retry_tail_exact`, `gaussian_retry_tail_bound`, `gaussian_retry_trials_law`: finite no-acceptance tails. |
| `GaussianRetryBatchTail.ec` | `grbt_prefix_shortfall_1m7`, `grbt_all_prefix_shortfall_limit`: batch shortfall and every-length limit. |
| `GaussianRetryInputs.ec` | `gr_candidate_stream_events`, `gr_candidate_stream_pairs_iid`, `gr_candidate_stream_accepted_iid`: canonical bytes and exact event sequences. |
| `GaussianRetryStreamBridge.ec` | `gr_sample_gauss_N_prefix_correct`, `gr_prefix_result_values`, `gr_prefix_result_frame`, `gr_prefix_result_squares`: adequate-prefix Hoare bridge. |
| `GaussianRetryPrefixCorrectness.ec` | `gr_prefix_failure_bound`, `gr_prefix_failure_limit`, `gr_block_prefix_failure_limit`: adequacy probabilities for finite byte prefixes. |
| `GaussianRetryRank.ec` | `grr_rank_step_bounded`: decreasing rank from a finite maximum of compatible block indices. |
| `GaussianRetryConsumerTotal.ec` | `gr_consumer_lossless`, `gs_progress_consume_total`, `gs_progress_consume_total_dynamic`: bounded actual consumer terminates and preserves stream progress. |
| `GaussianRetryBufferTotal.ec` | `gr_initial_squeeze_total`, `gr_carry_total`, `gr_refill_squeeze_total`: actual buffer operations terminate and preserve stream segments, with mutable inputs captured inside the contracts. |
| `GaussianRetryStreamTermination.ec` | `gr_sample_gauss_N_prefix_total`, conditional totality of the concrete SHAKE consumer. |

All 128 non-NTT targets passed fresh EasyCrypt checking as individual main
targets with `-no-eco`, `Proofs:check` and the EOF completion guard. The 113
unchanged independent targets were checked while the final new proof was
developed; the 15 new targets were then checked after their sources froze.
The collector uses the unchanged `verify-one.sh` runner and verifies the
complete inventory and every final source hash before reporting PASS. All 18 verification-gate regressions passed. The 140-file inventory
includes 12 retained NTT targets with unchanged hashes; they were not rerun
in this milestone. All 102 extractions matched fresh output, all previous
proof and production sources stayed unchanged, and no new project axiom was
introduced. Exact hashes and timing are recorded in `../VALIDATION.md` and
the verification manifest.

```
make -C haetae-1.2.0-easycrypt verify-new
make -C haetae-1.2.0-easycrypt test-gate
```
