# Hyperball witnesses through the actual extracted helpers

The earlier [numerical boundary record](hyperball-numerical-boundary.md)
separated two results: an EasyCrypt proof of integer norm/residue inequalities,
and an executable C/Jasmin comparison. The integer proof started with supplied
coefficients. This stage connects prescribed candidate bytes to the actual
extracted sampling, fixed-point, scaling and norm procedures, so the final
witness theorem derives those coefficients and acceptance results.

The producer-to-result endpoint is `HyperballWitnessReplay.run(mode)`, which
first invokes the candidate producer and then the execution driver. Its
integration and verification status is recorded below.

## Prescribed candidates and the two dummy squares

[HyperballWitnessSpec.ec](../theories/HyperballWitnessSpec.ec) defines one fixed
26-byte candidate for each mode and zero sign bytes. The expected samples,
square limbs, Newton intermediates, scale and final coefficients are also
definitions. Defining an expected value supplies no proof that a procedure
returns it; separate equalities and procedure contracts establish each link.

[HyperballWitnessCandidate.ec](../proofs/HyperballWitnessCandidate.ec) derives
the candidate's decoded inputs, CDT result, rounded sample, square limbs and
acceptance. `hbw_candidate_total` connects the complete tuple to
`SamplerTarget.M.__sample_gauss_sigma76_regs` with probability one.

[HyperballWitnessSampling.sample(mode)](../proofs/HyperballWitnessSampling.ec)
builds a buffer by repeating those
candidate bytes and calls the actual `__sample_gauss_at` consumer once per
polynomial. The request schedule is **257, 257, then 256** for every remaining
polynomial, with output offsets increasing by 256. Each call receives enough
bytes for its requested candidates. It produces 1,536, 2,304 or 2,816 stored
magnitudes from 1,538, 2,306 or 2,818 accepted events, respectively.

The last accepted event of each of the first two calls is an unstored dummy.
Both dummy squares enter the accumulator. The accumulated quantity is the sum
of the returned square limbs,
`uint(low) + 2^48*uint(high)`, over all accepted events. It is not replaced by
the sum of squares of the rounded stored magnitudes.

## Actual fixed-point and norm execution

[HyperballWitnessExecution.ec](../proofs/HyperballWitnessExecution.ec) defines
`HyperballWitnessExecution.run(mode,samples,signs,squares)`. It calls:

1. `_fixpoint_half_round` on the produced square accumulator.
2. `_fixpoint_newton_invsqrt`, including the first subtraction and six further
   Newton updates, with the mode's cube and three-halves constants.
3. `_fixpoint_mul_high` to obtain the scale.
4. `_sf_scale_and_check` to generate the two coefficient arrays and acceptance
   flag.
5. `_polyfixveclk_sqnorm2_2048` on those returned arrays to expose the norm word.

The returned tuple is `(out1,out2,accept,norm)`. Expected half, inverse, scale
and coefficient values are not arguments to this driver. `hbwe_total` connects
its result to the existing exact word specifications.

[HyperballWitnessNewton.ec](../proofs/HyperballWitnessNewton.ec) supplies the
numeric obligations: `hbw_newton_initial_exact`, `hbw_newton_exact`,
`hbw_scale_exact`, `hbw_magnitude_exact` and `hbw_coefficient_exact`.
Each intermediate certificate value must be proved as an EasyCrypt equality.
[HyperballWordEvaluation.ec](../proofs/HyperballWordEvaluation.ec) provides
checked integer division/modulo normal forms for the underlying word operations.
These retain every wrap and truncation; there is no numerical oracle.

The first-pair fixtures have signed high limbs -33,789,970, -157,935,164 and
-11,211,417. Their low limbs in modes 2 and 5 exceed `2^48`. The Newton proof
must connect these pairs to the actual first subtraction; checking the signs
of the fixture constants alone would leave that obligation open. The pinned
[C source](../../HAETAE-1.2.0/reference_implementation/src/fixpoint.c) also
explicitly allows a negative first estimate. Exact word replay establishes no
real inverse-square-root convergence theorem.

## Derived coefficient and norm observations

The following table is the final replay contract. Every active coefficient in
both output arrays is the listed signed 32-bit integer.

| Mode | Stored count | Signed coefficient | Integer squared norm `N` | `N mod 2^64` | Acceptance bound |
| --- | ---: | ---: | ---: | ---: | ---: |
| 2 | 1536 | -1704795102 | 4464117257937700460544 | 5192099988969472 | 6505809026482176 |
| 3 | 2304 | -334802028 | 258260884883511054336 | 6467851577331712 | 22510896139993088 |
| 5 | 2816 | -632138900 | 1125272442323279360000 | 21053826996711424 | 33503371683954688 |

The quotients `N div 2^64` are 242, 14 and 61. In every mode, the residue is
at most the bound while `N` exceeds it. The actual norm procedure returns the
64-bit reduction, and the acceptance flag follows that word comparison.

The recorded full rounded magnitudes before the final 32-bit conversion are
412929335944226, 448613294232468 and 545876826280812. Each exceeds `2^31-1`.
Consequently, a signed-fit lemma cannot justify these conversions. The replay
uses unconditional word semantics: with the prescribed zero sign bit, the
coefficient word is `W32.of_int M`; decoding its signed value yields the
negative coefficient in the table. The proof retains this conversion wrap.

[HyperballWitnessNorm.ec](../proofs/HyperballWitnessNorm.ec) connects constant
coefficient prefixes and output frames to the actual scaling and norm calls.
Its intermediate coefficient premise is discharged by
`hbw_coefficient_exact` in the final composition.
[HyperballWitnessArithmetic.ec](../proofs/HyperballWitnessArithmetic.ec) checks
the event budgets and the displayed norm/residue/bound arithmetic.

## Scope and reproduction

This deterministic driver supplies candidates and signs directly. It supplies
no producing SHAKE seed, does not run the full seeded Hyperball procedure, and
does not prove reachability within its retry loop. The witness demonstrates why
the word acceptance condition does not by itself imply the geometric integer
norm bound.

The existing [C/Jasmin replay](../tests/hyperball-norm-boundary.py) has been rerun
successfully for this stage. Its [C probe](../tests/hyperball-norm-boundary.c)
compares the pinned reference, compiled Jasmin and recorded observations.
This remains an experimental C comparison, not a formal C proof or a formal
C/Jasmin equivalence theorem. The reference constants and their input hashes
are recorded in
[HyperballReferenceConstants.ec](../theories/HyperballReferenceConstants.ec).

From the repository root:

```sh
python3 haetae-1.2.0-easycrypt/tests/hyperball-norm-boundary.py
make -C haetae-1.2.0-easycrypt verify-new
make -C haetae-1.2.0-easycrypt test-gate
```

An individual proof can be checked from the EasyCrypt project directory:

```sh
bash scripts/verify-one.sh proofs/HyperballWitnessExecution.ec
```

The verifier enables proof checking, disables cached `.eco` files and appends
a checked EOF declaration so an unfinished proof cannot pass at end of input.

**Verification status: PASS.** All 9 new sources passed individual and
integrated fresh main-target checks. The complete non-NTT gate passed
160/160 targets with `-no-eco`, `Proofs:check` and the EOF completion
guard. It checked the 151 unchanged targets first, then the 9 frozen new
targets, followed by final inventory/hash comparisons. The 172-file local
inventory includes 12 unchanged NTT targets with retained prior checks; they
were not rerun in this stage. All 18 gate regressions passed and all 102 fresh
extractions matched. The prescribed C/Jasmin replay passed all three modes.
Production code did not change and KAT was not rerun in this proof stage.

`hbwr_total` derives the detailed returned-array/coefficient/norm/acceptance
contract from only mode2/3/5 and the constructed input experiment.
`hbwr_accepted_outside_radius_total` states directly that this experiment
terminates with accepted word1 and mathematical norm above the mode's bound,
with probability one. `hbw_sampling_total` supplies the actual finite-consumer
outputs, including both dummy squares; expected intermediates are not premises
of the final replay theorem. Source hashes, exact commands and timing are
recorded in [VALIDATION.md](../VALIDATION.md) and the verification manifest.

The subsequent [input safe-domain proof](hyperball-safe-domain.md) derives numerical
safety from a sufficient canonical entry-square interval. The prescribed
examples above are formally shown to lie outside that interval. This does not
classify every outside input or bound the probability of leaving the interval.
