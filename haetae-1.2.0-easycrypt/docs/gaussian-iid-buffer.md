# Gaussian buffered sampling with independent uniform bytes

This milestone connects a buffer controller that draws independent uniform
bytes to the joint distribution of its **256 visible unsigned magnitudes**.
The controller calls the extracted Jasmin sign-copy, carry and finite Gaussian
consumer procedures. Its randomness is an explicit byte distribution.

All 16 new source files passed individual and integrated fresh checks.
The complete non-NTT replay passed 144 targets with `-no-eco`, `Proofs:check`
and the EOF completion guard; 18 gate regressions passed. The 128 unchanged
targets were checked while new proofs were developed, then the 16 frozen new
targets were checked. Final inventory and source hashes were compared before
PASS. The 156-file inventory includes 12 unchanged retained NTT targets that
were not rerun in this milestone. All 102 fresh extractions matched.
The [target manifest](../manifests/proof-targets.txt) and
[verification results](../manifests/verification-results.json) record the exact
inventory, source hashes, commands and timing.

## Uniform bytes and exact candidate observations

`gbc_bytes n = dlist W8.dword n` is a list of independent uniform octets.
`gbc_candidate = BArray26.darray` is the installed distribution that samples
26 such bytes and constructs a byte array. It covers all 208 input bits.

The sampler uses 83 CDT bits, 48 rejection bits and 72 noise bits. The high
five bits of byte 10 do not affect its computation. `gub_canonical` masks that
byte with 7, and `gub_sigma76_spec` preserves the entire four-word result:
rounded magnitude, both square limbs and acceptance word. This identity holds
for every input array, including rejected candidates.

`gbc_canonical_law` identifies the canonical projection of the uniform array
with `gr_candidate_distribution p`, the independent 83/72/48-bit model, for
arbitrary base template p. The projected arrays have zero unused bits.
`gbc_candidate_sigma_law` consequently preserves the full four-word event
distribution; `gbc_candidate_observer_law` gives the exact pair law

```
dmap gbc_candidate
  (fun bytes => (uint((sigma76_spec bytes).1),
                 (sigma76_spec bytes).4 = W64.one))
  = sc_actual_pair p.
```

The proof uses integer radix bijections and uniform-list splitting.
`gbc_chunks_iid` groups any finite list of 26*n uniform bytes into n independent
uniform candidate arrays. No distribution over infinite byte functions is
needed.

## Operational buffer controller

[GaussianIidBufferSpec.ec](../theories/GaussianIidBufferSpec.ec) defines
`GaussianIidBuffer.sample`. Each block draw has law
`gib_block = dlist W8.dword 136`. The controller:

1. Draws 49 blocks, filling 6,664 bytes.
2. Calls `GIBSigner.__sample_gauss_N_copy_signs_at` for the first 32 bytes.
3. Calls `GIBSigner.__sample_gauss_at` on the remaining 6,632 bytes: 255
   complete candidates and a two-byte remainder.
4. While the accepted count is below the request, calls
   `GIBSigner._sample_gauss_N_carry`, appends a fresh 136-byte block and calls
   the finite consumer again. The remainder always has length below 26.

`GIBSigner` is `ApiTarget.M(ApiTarget.Syscall)`. The path proof relates these
actual helper calls to `GaussianIidBufferFunctional`, whose list state records
the exact pending bytes and whose `gib_consume` retains the word-level trace.
`gib_actual_functional` relates the complete returned arrays under a coupling
of the same block draws. The finite initialization equivalence
`gib_initial_uniform_equiv` then replaces the 49 concatenations with one
uniform 6,664-byte draw for the probability argument.

The public input condition is exactly `gib_bounds n offset signoff`:

```
n = 256 or n = 257
0 <= offset,  offset + n <= 4096
0 <= signoff, signoff + 32 <= 512.
```

The initial output, sign and square arrays are arbitrary. The current word
model requires neither an adequate-prefix witness nor canonical initial square
limbs. Separate interpretations of the accumulator as an unbounded integer sum
retain their prior initial-limb and range/headroom hypotheses.

## A continuation law for the literal carried tail

A carried tail can depend on the execution history. The loop proof therefore
keeps its actual bytes, rather than assigning them a new uniform law.

For visible accepted values v and a fixed byte list tau with length below 26,
`gik_kernel v tau` draws only the missing bytes of the next candidate, processes
that completed candidate and uses the conditioned completion distribution for
the remaining visible demand. The following identity is pointwise in tau:

```
draw block uniformly from 136 fresh bytes;
scan complete candidates in tau ++ block;
continue with the literal leftover bytes
```

has distribution `gik_kernel v tau`. `gbc_fixed_tail_refill` and
`gik_refill_complete` establish this identity. Fresh suffixes may be combined
using finite independent-byte laws; no freshness premise is imposed on the
carried bytes.

The event proof uses `mu (gik_kernel visible tail) event` as its loop potential.
At 256 visible values this continuation is a point mass. This remains true
while a request for 257 is still waiting for its accepted dummy.

## Termination and the exact visible joint law

Termination has a separate argument. For every fixed tail of length below 26,
the second complete candidate in a refill lies wholly inside the fresh block.
Its acceptance probability is at least 1/7. Consequently, while work remains,
the bounded deficit `n-accepted` decreases with probability at least 1/7 and
never increases. `git_functional_total` supplies probability-one termination;
the operational equivalence transfers it to the controller with actual helper
calls.

`gie_uniform_event_upper` supplies an upper bound for each visible-list event.
The public argument applies that bound both to the event and its complement.
Together with independently established termination and a lossless target,
the two bounds give equality. An event upper bound alone is not used as an
exact distribution law.

Write `A_p = sc_actual_conditioned p`. The target is

```
gid_target = dlist (gr_output gik_pairs) 256 = dlist A_p 256.
```

Under `gib_bounds`, the public contracts `gii_actual_joint_law` and
`gii_actual_terminates` state, for every event E on ordered integer lists,

```
Pr[GaussianIidBuffer.sample(...): E(gib_magnitudes res offset)]
  = mu gid_target E
Pr[GaussianIidBuffer.sample(...): true] = 1.
```

These statements cover both requested counts 256 and 257. `gib_magnitudes`
always reads exactly the 256 words at positions offset through offset+255.

For the independent Gaussian from
[Gaussian magnitude identification](gaussian-magnitude-identification.md),

```
Pr[G=k] = exp(-k*k/2^153) / sum_{j in Z} exp(-j*j/2^153)
R       = floor((abs(G)+32768)/65536),
```

the previous single-output bound is `SDist(A_p, law(R)) < 2^-39`.
`gii_target_gaussian` applies the ordered-product bound to obtain

```
SDist(gid_target, dlist law(R) 256) < 2^-31.
```

`gii_actual_gaussian_event` expresses the same bound for every event on the
controller's whole visible vector. `gii_actual_correct` bundles termination,
the exact visible law and this Gaussian comparison. These public contracts were included in the fresh integrated replay.

## State observations and scope

The pathwise model retains the actual sign-byte copy and its frame, carries the
exact byte remainder, preserves output outside the committed window, and
retains speculative rejected writes. Its square state follows the two raw
square limbs returned by each accepted attempt and the word normalization
operations, including modular word arithmetic. It does not substitute the
square of the rounded magnitude or add an unconditional no-wrap integer-sum
interpretation.

With requested count 257, the last accepted event is counted and contributes
its square limbs, but its magnitude is not written to the dummy output slot.
The earlier full-257 mathematical batch observer is separate from that
unwritten physical slot, which retains its input value. The visible law here
concerns the ordered first 256 stored magnitudes.

The copied sign bytes remain part of the pathwise state. This milestone makes
no sign-distribution, sign-independence or sign-application claim, and does not
give a complete Gaussian joint law for the returned output/sign/square triple.
Concrete SHAKE, signed outputs, Hyperball sampling and complete signature APIs
remain separate proof boundaries. The concrete-SHAKE adequate-prefix results
in [the retry documentation](gaussian-retries-and-batches.md) keep their own
premises; they are not replaced by an unconditional statement about every seed.

## Proof map

| Sources | Role |
| --- | --- |
| [MixedRadixUniform](../proofs/MixedRadixUniform.ec), [GaussianUnusedBits](../proofs/GaussianUnusedBits.ec), [GaussianUniformBytes](../proofs/GaussianUniformBytes.ec) | Genuine uniform bytes, canonical projection, complete attempt tuples and finite candidate grouping. |
| [GaussianIidBufferSpec](../theories/GaussianIidBufferSpec.ec), [GaussianIidBufferPath](../proofs/GaussianIidBufferPath.ec) | Operational controller, actual helper contracts and full-state functional equivalence. |
| [GaussianByteCarryDistribution](../proofs/GaussianByteCarryDistribution.ec), [GaussianIidKernel](../proofs/GaussianIidKernel.ec) | Fixed literal-tail continuation and exact refill identity. |
| [GaussianIidVisible](../proofs/GaussianIidVisible.ec), [GaussianIidStep](../proofs/GaussianIidStep.ec) | Visible-prefix updates, frames and request-257 dummy handling. |
| [GaussianIidInitial](../proofs/GaussianIidInitial.ec), [GaussianIidNormalization](../proofs/GaussianIidNormalization.ec) | 49-block initialization normalized to one uniform draw. |
| [GaussianIidProgress](../proofs/GaussianIidProgress.ec), [GaussianIidTermination](../proofs/GaussianIidTermination.ec) | Uniform fresh-candidate progress and independent termination proof. |
| [GaussianIidEventLaw](../proofs/GaussianIidEventLaw.ec) | Expectation-Hoare event upper bound with the literal tail in the invariant. |
| [GaussianIidDistribution](../proofs/GaussianIidDistribution.ec) | Public visible joint law and `2^-31` comparison. |

## Reproduction

Run from the repository root:

```sh
make -C haetae-1.2.0-easycrypt check-extraction
make -C haetae-1.2.0-easycrypt verify-new
make -C haetae-1.2.0-easycrypt test-gate
```

For focused development replays, from the project directory:

```sh
cd haetae-1.2.0-easycrypt
bash scripts/verify-one.sh proofs/GaussianUniformBytes.ec
bash scripts/verify-one.sh proofs/GaussianIidDistribution.ec
```

The runner uses `-no-eco`, explicit `Proofs:check` and an EOF completion guard.
Set `WHY3_SERVER_SOCKET` only when using an already running Why3 server.
The `verify-new` gate checks each selected local theory or proof as an
independent main target. A focused replay does not replace that complete check.
Consult the final verification manifest and [VALIDATION.md](../VALIDATION.md)
for the published result and exact inventory.
