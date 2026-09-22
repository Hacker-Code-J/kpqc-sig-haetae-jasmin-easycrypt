# Hyperball iid square tails and one-attempt unsafe acceptance

Verification status: PASS.

Proof integration and the complete fresh source gate passed; the evidence is recorded below.

This stage bounds two events in the explicit iid-byte model: the raw square
sum leaving the sufficient numerical safety interval, and one attempt both
accepting and returning coefficients whose integer squared norm exceeds the
mode's bound. Both events have the following strict upper bounds:

| Mode | Full accepted payload count D | Bound for either event |
| --- | ---: | ---: |
| 2 | 1,538 | `< 2^-29` |
| 3 | 2,306 | `< 2^-44` |
| 5 | 2,818 | `< 2^-54` |

The bounds concern an explicit uniform-byte experiment using the actual
Gaussian helpers and actual numerical-tail calls. They do not state that
the same random-input law holds for a concrete SHAKE seed.

## The random variable and initialization

Let `Q = 2^76`, and let `Z = 2^72*x + y` be the candidate before rounding,
where `x` is the actual CDT output and `y` the decoded 72-bit noise. For
each candidate, `GaussianRawSquare.gps_square_exact` identifies the raw
payload square exactly:

```text
q = uint(square_low) + 2^48 * uint(square_high)
  = floor(Z^2 / Q)
X = q / Q
```

The floor is part of the implemented computation. This `q` is not the square
of the rounded magnitude returned to the sample array.

The accepted-payload distribution is the existing `gpd_accepted`: observe
the actual sigma computation on 26 independent uniform bytes, condition on
its acceptance, and retain its magnitude and raw square together. The
[full-payload result](gaussian-payload-and-squares.md) gives the complete
history as `dlist gpd_accepted D`. The same history determines the visible
sample vector and `S = sum q`; no independence between that vector and S
is assumed. Zero-based history positions 256 and 513 are omitted only from
the visible magnitudes. Both squares remain in S.

The batch starts with square accumulator zero, requests `257, 257, 256, ...`,
and uses sample offsets `256*i` and sign offsets `32*i`. Its `hip_initial`
also zeros the sample and sign arrays as a choice of the proof model.
Production [`sign.jazz`](../../haetae-1.2.0-jasmin/jasmin/sign.jazz), at
lines 1201–1202, initializes only `sqsum`; it does not zero those stack
arrays. The actual call schedule, offsets, active outputs and square
accumulation are linked within the explicit iid model. This is not a
whole-state equivalence to production initialization or seeded Hyperball.
Ghost erasure within the iid model preserves the whole returned triple.

## Actual accepted exponential moments

The moment bounds concern the implemented, acceptance-conditioned raw
square, including its floor. With expectation over `gpd_accepted`:

```text
E[exp((19/200)*X)] <= 10/9 + 2^-18
E[exp(-(15/98)*X)] <= 7/8 + 2^-18
```

`GaussianSquareMoments.gsm_plus_bound` and `gsm_minus_bound` discharge these
bounds. Their proof connects the raw-square payload to bounded weighted
acceptance expectations, accounts for the actual acceptance denominator,
and compares the ideal weighted sums with integer Gaussian lattice sums.
It keeps truncation and implementation errors in the moment budget.
The raw-square observation retains information lost by output rounding,
so its moment bounds are derived separately from the rounded-magnitude law.

The resulting centered bounds are:

```text
E[exp((19/200)*(X - 5/4))] <= r+ = 3947/4000
E[exp((15/98)*(3/4 - X))] <= r- = 1963/2000
```

`gsm_centered_plus` and `gsm_centered_minus` combine the moments with the
checked real exponential inequalities
`exp(-19/160)*(10/9 + 2^-18) <= r+` and
`exp(45/392)*(7/8 + 2^-18) <= r-`.

## Checked constants and iid tail argument

[`hyperball-tail-certificate.py`](../scripts/hyperball-tail-certificate.py)
generates exact integer interval data. The scale is `2^128`; rational seeds
and 32 outward squarings enclose the negative exponentials; the positive
factor follows from `exp(a)*exp(-a)=1`. Short binary
power chains enclose `(r+)^D` and `(r-)^D`. EasyCrypt checks every seed,
interval multiplication, exponent transition and final integer comparison.
`HyperballTailConstants` separately proves the analytic exponential and
power interpretation. Python supplies data, not a numerical oracle or an
assumed inequality. `--check` verifies byte-for-byte reproducibility.

`IidExponentialTail` proves the expectation product identity and the
nonnegative exponential tail bounds for finite iid lists. Applying it to
the accepted raw-square history yields:

```text
Pr[S < (3D/4)*Q or (5D/4)*Q < S]
  <= (r+)^D + (r-)^D
  < epsilon(mode)
```

The final certificate supplies `epsilon(2)=2^-29`, `epsilon(3)=2^-44`, and
`epsilon(5)=2^-54`. The safe interval is closed: equality at either endpoint
belongs to the safe event. The previous batch proof supplies canonical
limbs and exact integer accumulation, so the public tail theorem has no
additional canonical-output, moment or desired-tail-bound premise.

## Actual numerical tail and the unsafe event

`HyperballIidAttempt.sample` first calls the iid Gaussian batch and then
`HyperballSafeExecution.run` on its returned sample, sign and square arrays.
The latter composes the actual half, six-step Newton, scaling and norm
helpers. The input-safe-domain theorem proves that acceptance from a safe
entry square sum implies the integer radius condition. Consequently:

```text
Pr[accepted AND integer_squared_norm > uint(hb_ref_bound mode)]
  <= Pr[S outside the sufficient safe interval]
  < epsilon(mode)
```

Here `accepted` is the actual returned word equal to `W64.one`, and the
integer squared norm is `hsc_norm` of the returned signed32 coefficients,
not the modular norm word. `hia_unsafe` names this conjunction.

This is an unconditional probability for one iid attempt. It is not
`Pr[bad | accepted]`: the proof does not divide by Hyperball's acceptance
probability. The sufficient interval also does not classify every outside
input as unsafe. The iid one-attempt procedure terminates with probability
one; this statement does not concern an outer retry loop.

## Public contracts

| File | Public contract | Scope |
| --- | --- | --- |
| [GaussianSquareMoments](../proofs/GaussianSquareMoments.ec) | `gsm_plus_bound`, `gsm_minus_bound`, `gsm_centered_plus`, `gsm_centered_minus` | Actual accepted raw-square moments and centered rational caps. |
| [HyperballTailConstants](../proofs/HyperballTailConstants.ec) | `ht_factor_plus`, `ht_factor_minus`, `ht_mode_power_bound` | Analytic exponential factors and exact mode-specific sums of powers. |
| [HyperballIidTailCorrectness](../proofs/HyperballIidTailCorrectness.ec) | `ht_iid_list_tail` | Full accepted-payload list's square-sum escape probability. |
| [HyperballIidTailCorrectness](../proofs/HyperballIidTailCorrectness.ec) | `ht_iid_square_tail`, `ht_iid_square_interval` | Actual-call iid Gaussian batch's safe-domain complement and explicit integer interval event. |
| [HyperballIidTailCorrectness](../proofs/HyperballIidTailCorrectness.ec) | `ht_iid_unsafe_acceptance`, `ht_iid_accepted_outside_radius` | One actual-call iid attempt's joint acceptance/excessive-integer-norm event. |
| [HyperballIidTailCorrectness](../proofs/HyperballIidTailCorrectness.ec) | `ht_iid_unsafe_mode2`, `ht_iid_unsafe_mode3`, `ht_iid_unsafe_mode5` | The respective strict bounds `2^-29`, `2^-44`, `2^-54`. |

The public tail endpoints require only the supported-mode predicate; the
numerical endpoints specialize it. The generic intermediate
`ht_list_tail_from_moments` exposes moment assumptions for reuse, while
`ht_iid_list_tail` discharges them with the actual moment theorems.

## Remaining scope

This stage does not identify S with an ideal Gaussian-square or chi-square
law, bound the unsafe probability conditioned on Hyperball acceptance, or
bound an unbounded sequence of outer retries. It does not prove concrete
SHAKE pseudorandomness, full seeded Hyperball distribution or termination,
or complete KeyGen/Sign/Verify correctness. It adds no runtime input guard.
Earlier iid Gaussian retry and finite-batch termination theorems retain
their stated scope.

The [previous payload stage](gaussian-payload-and-squares.md) established an
exact square-law identity and left a numerical tail bound open. The present
stage adds that bound for the explicit iid model; it does not change the
earlier source files or enlarge their original theorem statements.

<!-- hyperball-tail:verification:start -->
## Verification evidence

All 15 added theory/proof sources passed fresh main-target checks with the
180 unchanged non-NTT sources: **195/195 PASS**, using `-no-eco`, explicit
`Proofs:check` and the EOF completion guard. The final inventory and source
hashes matched. The complete local inventory has 207 files. The 12 NTT
targets retain prior checks and unchanged source hashes; they were not
rerun in this milestone. Gate timestamp: `20260922T065900.431316Z`.

All 496 pinned old sources, including the preceding 192 local theory/proof
files, are unchanged. All 18 verification-gate regressions passed and 102
fresh extractions matched. The four installed tool executables retain the
recorded hashes. Certificate reproduction with `--check` passed with
matching generator and certificate hashes. The certificate's arithmetic
and analytic meaning are proved separately in EasyCrypt.

No new project axiom or numerical oracle was introduced. Production code,
reference sources, archived proofs and previous checkers/tests are unchanged.
KAT was not rerun. See [verification evidence](../manifests/verification-results.json),
[source correspondence](../manifests/specification-sources.json) and the
[complete target inventory](../manifests/proof-targets.txt).

Frozen EasyCrypt sources added in this stage:

- [GaussianLatticeMgf](../proofs/GaussianLatticeMgf.ec)
- [GaussianLatticeSum](../proofs/GaussianLatticeSum.ec)
- [GaussianPayloadMoments](../proofs/GaussianPayloadMoments.ec)
- [GaussianRawSquare](../proofs/GaussianRawSquare.ec)
- [GaussianSquareMoments](../proofs/GaussianSquareMoments.ec)
- [HyperballIidAttemptSafety](../proofs/HyperballIidAttemptSafety.ec)
- [HyperballIidTailCorrectness](../proofs/HyperballIidTailCorrectness.ec)
- [HyperballTailCertificateChecks](../proofs/HyperballTailCertificateChecks.ec)
- [HyperballTailConstants](../proofs/HyperballTailConstants.ec)
- [IidExponentialTail](../proofs/IidExponentialTail.ec)
- [RawSquareAcceptance](../proofs/RawSquareAcceptance.ec)
- [RawSquareIdealMoments](../proofs/RawSquareIdealMoments.ec)
- [HyperballTailCertificate](../theories/HyperballTailCertificate.ec)
- [HyperballTailSpec](../theories/HyperballTailSpec.ec)
- [RawSquareMomentSpec](../theories/RawSquareMomentSpec.ec)
<!-- hyperball-tail:verification:end -->
