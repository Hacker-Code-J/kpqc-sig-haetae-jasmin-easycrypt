# Target mode-2 first-attempt FFT input reachability

## Scope

This milestone connects the coefficient premise of the rounded FFT safety
proof to the five slices actually supplied to `_singular_full` by the exposed
first attempt of mode-2 key generation. It closes that premise for the
immutable first-attempt trace only. The residual retry loop remains in the
relational mirror but is not given a per-attempt semantic trace here.

The bridge is kept in
`easycrypt/refinement/TargetKeygenM23SingularFFTInputBounds.ec` because it
consumes target-refinement sampler and finalizer facts. The generic FFT bounds
remain in `easycrypt/spec/` and retain their reusable input premise.

## Five actual slices

`mode2_slice s1 final_s2 slot` selects exactly:

- slots `0`, `1`, and `2`: the three 256-word polynomials in sampled `s1`;
- slots `3` and `4`: the two 256-word polynomials in finalized `s2`.

For the first three slots, `mode2_sampler_facts` supplies the centered eta
range `[-1, 1]`, which immediately implies coefficient magnitude at most two.

For the final two slots, the same sampler facts place the pre-finalized `s2`
coefficient in `[-1, 1]`. `finalize_semantic_output` identifies the stored
coefficient as

```text
sampled_s2 - vk_low_int(raw_residue)
```

and `vk_low_int_range` places the low term in `[-1, 1]`. The finalized
coefficient is therefore in `[-2, 2]`. The proof uses the actual slice offsets
and covers every one of the 256 coefficients in each slot.

`mode2_fft_inputs_bound2_of_mode2_sampler_finalize` packages these cases as
`mode2_fft_inputs_bound2 s1 final_s2`. The direct corollaries then establish,
for every valid slot and every threaded scratch array:

- `actual_fft_schedule_safe data (mode2_slice s1 final_s2 slot)`; and
- the final `fft_word_bound` of `859963392` after all eight rounds.

The arbitrary scratch parameter matters because `_singular_full` threads one
FFT workspace through all five slice calls; the initializer overwrites the
active FFT cells before the schedule begins.

## First-attempt target trace

`TargetKeygenM23FullFirstAttempt` now exposes:

- `first_attempt_snapshot_fft_inputs_bound2` for the immutable trace;
- `first_attempt_snapshot_fft_slot_schedule_safe` for every valid slot;
- `first_attempt_snapshot_fft_slot_full_word_bound2` for the raw endpoint; and
- `mode2_full_first_attempt_fft_inputs_bound2_correct`, a Hoare theorem that
  retains the existing snapshot facts and adds the five-slice predicate.

This is stronger than assuming `fft_coefficient_bound xp 2` at an isolated FFT
call: the premise is derived from the sampler and finalizer facts carried by
the actual peeled first attempt.

## Deliberate boundary

The result does not prove:

- the same facts for a rejected attempt executed by the residual retry loop;
- the owner-stage rounded-machine-to-ideal error recurrence;
- squared-magnitude or five-pass accumulator nonoverflow;
- analytic correspondence of the machine score with the paper statistic;
- first-attempt acceptance or retry termination; or
- packing or public-key-generation correctness.

In particular, the raw FFT coordinate bound must not be squared to justify the
accumulator. That path requires a sharper spectral safe-trace theorem, a
quantified unsafe event, or wider implementation arithmetic.

## Verification

Run:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-m23-matrix-proof.sh
```

The gate compiles the reachability bridge before the first-attempt target
theory with `-no-eco`, then runs the proof-hole, authored-axiom, and debug scan.
