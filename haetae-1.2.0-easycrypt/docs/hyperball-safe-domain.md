A canonical raw square accumulator in the interval below gives a sufficient
input condition for the Hyperball scaling and norm check to have an exact
integer interpretation. The condition concerns the input accumulator; it does
not assume a bounded inverse, scale, output coefficient or output norm.

**Verification status: PASS.** All 8 new sources passed individual and
integrated fresh main-target checks. The complete non-NTT gate passed
168/168 targets with `-no-eco`, `Proofs:check` and the EOF completion
guard. The 160 unchanged targets were checked first, then all 8 frozen
new targets, with final inventory/hash checks. The 180-file inventory
includes 12 unchanged NTT targets whose previous checks were retained rather
than rerun. All 18 gate regressions passed and all 102 fresh extractions matched.

`hsc_total` establishes the complete finite numerical-tail result from the
input predicate alone; `hsc_accepted_radius_total` states the accepted-radius
consequence directly. `hsc_full_magnitude` derives the full pre-conversion
coefficient magnitude bound. The predicate is a proof precondition; this stage
adds no runtime input guard or change to production code. KAT was not rerun.

Let `R = 2^48`, `Q = 2^76`, and
`S = hb_value (hb_load squares) = uint(low) + R*uint(high)`.
[HyperballSafeSpec.ec](../theories/HyperballSafeSpec.ec) defines the input
predicate `hbs_good` by exactly these conditions:

- The mode is 2, 3 or 5.
- The initial low limb is canonical: `uint(low) < R`.
- `3*D*Q/4 <= S <= 5*D*Q/4`, where `D` is the stored count plus two.

The two extra events are the unstored final samples of the first two
257-sample Gaussian calls. Their raw square limbs still enter the accumulator.
Thus, when `squares` comes from sampling, `S` is the accumulated integer value
of the raw square limbs over all accepted events. It is not the sum of squares
of the rounded stored magnitudes. The
[finite-consumer witness driver](../proofs/HyperballWitnessSampling.ec)
illustrates this distinction with its 257, 257, then 256 request schedule.

| Mode | Stored count | `D` | Inverse value cap `H` |
| --- | ---: | ---: | ---: |
| 2 | 1536 | 1538 | `Q/32 = 2361183241434822606848` |
| 3 | 2304 | 2306 | `7*Q/256 = 2066035336255469780992` |
| 5 | 2816 | 2818 | `23*Q/1024 = 1697100454781278748672` |

These caps are `hbs_inverse_cap` in the shared specification.
[HyperballSafeConstants.ec](../proofs/HyperballSafeConstants.ec) connects them
to the mode constants and checks the required numeric margins. Its
`hbs_center_good` certificate supplies a concrete valid accumulator in every
mode: low zero and high `D*2^28`, giving `S = D*Q`. This establishes that the
input interval is nonempty; it supplies no probability that sampling enters it.

The public procedure is
`HyperballSafeExecution.run(mode,samples,signs,squares)`. Its sample and sign
arrays are arbitrary. In particular, the contract requires no relationship
between their contents and `S`, and no uniformity or independence assumption.
`HyperballSafeExecution` aliases the existing generic
[HyperballWitnessExecution](../proofs/HyperballWitnessExecution.ec). That
driver calls the [actual extracted](../generated/api/ApiTarget.ec) `_fixpoint_half_round`,
`_fixpoint_newton_invsqrt`, `_fixpoint_mul_high`, `_sf_scale_and_check`, and
`_polyfixveclk_sqnorm2_2048` procedures. It returns
`(out1,out2,accepted,norm_word)` and receives no expected intermediate results.

The proof connects the input interval to the final integer interpretation as
follows:

1. Half-rounding gives the exact integer `(S+1) div 2`. The mode certificates
   bound the initial product and give a subtraction gap of at least `R`.
   [HyperballPositiveArithmetic.ec](../proofs/HyperballPositiveArithmetic.ec)
   then interprets the first subtraction exactly. Its low limb may be below
   `2R` rather than `R`, so the first Newton state retains that extra bit.
   The positive gap prevents a wrapped high limb from being mistaken for an
   unsigned mathematical difference.
2. [HyperballMulBounds.ec](../proofs/HyperballMulBounds.ec) handles operands
   with low below `2R` and value at most `2^88`. Multiplication returns a value
   between `floor(X*Y/Q)` and that floor plus one; therefore its scaled
   error has absolute value at most `Q`. Squaring returns exactly
   `floor(X^2/Q)`. The square operation therefore has different rounding from
   general multiplication.
3. [HyperballNewtonBarrier.ec](../proofs/HyperballNewtonBarrier.ec) bounds the
   cubic Newton update with enough margin to absorb those integer rounding
   errors. The intermediate `u` stays at most `5Q/4`, so the correction
   `3Q/2-u` lies between `Q/4` and `3Q/2`. Its high word is positive and its
   sign bit is zero. The actual signed multiplication consequently agrees
   with the ordinary word multiplication. This invariant is composed through
   all six updates in
   [HyperballSafeNewton.ec](../proofs/HyperballSafeNewton.ec), yielding a
   canonical final inverse with integer value at most the mode's `H`.
4. [HyperballSafeScale.ec](../proofs/HyperballSafeScale.ec) propagates that cap
   through the actual multiplication by the mode scale constant. The scale
   value is at most `2^85`. For every 64-bit sample word, the implemented
   rounded coefficient magnitude `M` is then at most `2^26`. Either extracted
   sign gives a signed 32-bit value in `[-2^26,2^26]`, so the final conversion
   fits. Here `M` denotes the magnitude after the implemented multiplication
   and rounding, not an ideal real product.
5. There are at most 2816 active coefficients. Their mathematical squared norm
   `N` therefore satisfies `0 <= N <= 2816*2^52 < 2^64`.
   [HyperballNormSpec.ec](../theories/HyperballNormSpec.ec) supplies this
   counting bound, and
   [HyperballNormCorrectness.ec](../proofs/HyperballNormCorrectness.ec) links
   the extracted norm procedure to the word encoding of `N`. The range
   removes the final modulo: `uint(norm_word) = N`.

The proved postcondition is `hsc_result`: both active coefficient prefixes
obey the `2^26` bound, the norm word decodes to the full integer norm, and
`accepted = W64.one` holds exactly when
`N <= uint(hb_ref_bound mode)`. Acceptance therefore implies the mode's
integer squared-radius bound in this input domain. This is a conditional
norm-safety statement, not a guarantee that the attempt is accepted.

The earlier [prescribed overflow witnesses](hyperball-actual-witnesses.md)
remain valid word executions. `hsc_prescribed_witness_outside` establishes
that their recorded raw square sums fail `hbs_good`; their exclusion follows
from the input interval, without inspecting or assuming their output norm.

This stage covers the finite scaling-and-checking execution under the stated
input predicate. It proves neither termination of the outer rejection loop
nor a probability of reaching the interval. It also supplies no real
inverse-square-root accuracy theorem and no assertion that concrete SHAKE
outputs are independent random inputs.

Run the project checks from the repository root:

```sh
make -C haetae-1.2.0-easycrypt verify-new
make -C haetae-1.2.0-easycrypt test-gate
```

For an individual proof, run from the EasyCrypt project directory:

```sh
bash scripts/verify-one.sh proofs/HyperballPositiveArithmetic.ec
bash scripts/verify-one.sh proofs/HyperballSafeCorrectness.ec
```

The runner enables `Proofs:check`, disables cached `.eco` files and appends a
completed EOF declaration to reject unfinished proofs. When using the shared
solver, prefix an individual command with
`env WHY3_SERVER_SOCKET=/tmp/haetae120-easycrypt-20260917.socket`.
Final verification evidence is recorded in [VALIDATION.md](../VALIDATION.md).
