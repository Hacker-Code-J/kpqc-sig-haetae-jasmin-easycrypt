# Target mode-2 FFT accumulator trace

## Scope

This milestone bridges the rounded Q16 squared-magnitude helper to the exact
complex energy that feeds the mode-2 accumulator. The actual helper is
`KeygenM23SingularSpec.fft_sqabs_at`, and the running update is
`KeygenM23SingularSpec.accumulate_step` threaded through
`KeygenM23SingularSpec.accumulate_prefix` across `singular_words_i = 256`
slots. In the actual first-attempt trace, exactly five accumulator updates
matter: three sampled `s1` slices followed by two finalized `s2` slices.

The bridge is conditional on `KeygenM23SingularBoundary.fft_accumulate_safe`
at every step. It does not claim accumulator safety from coefficient bounds,
and it does not speak about score correspondence, acceptance, retry
termination, or any later-loop attempt.

## Local decode

The checked integer semantics already expose the local decoded step:
`fft_sqabs_at_to_sint` proves the rounded squared magnitude under
`fft_sqabs_safe`, `accumulate_step_at_to_sint` proves one pointwise
accumulator update under `fft_accumulate_safe`, and `accumulate_step_frame`
preserves every other accumulator entry.

The local rounded squared magnitude uses two `W32` Q16 self-products and one
`W32` add. Each self-product has decoded rounding error at most `1/131072`,
so the decoded `fft_sqabs_at` value is within `1/65536` of the exact
`cnorm2` energy of the underlying complex slot.

The bridge lifts that local step with the componentwise complex perturbation
bound
`eps * (2 * abs(ideal_re) + eps) + eps * (2 * abs(ideal_im) + eps)`,
which is the exact shape needed to move from `cclose eps` on the real and
imaginary coordinates to the squared-norm difference.

`KeygenM23SingularFFTAccumulatorBridge.fft_sqabs_decode_error` records that
local `1/65536` bound. `cclose_cnorm2_perturbation` lifts a componentwise FFT
error to exact complex energy, and
`accumulate_fft_sqabs_decode_ideal_step` combines both facts with the decoded
running update.

## Prefix trace

`mode2_actual_accumulate_prefix_error` threads an explicit energy/error
recurrence over any valid prefix of the five actual mode-2 slices. The
recurrence is pointwise and evolving: it accumulates the ideal `cnorm2`
energy prefix, adds the local `1/65536` rounding budget and the propagated FFT
coordinate budget, and checks `fft_accumulate_safe` on the exact pre-step
accumulator and FFT output. `mode2_actual_accumulate_full_error` specializes
that induction to all five slices.

`TargetKeygenM23FirstAttemptAccumulator.first_attempt_snapshot_accumulator_error`
uses the immutable first-attempt snapshot to discharge coefficient bound two
for the three `s1` and two finalized-`s2` inputs. It retains
`first_attempt_trace_accumulator_safe` as a separate premise. That boundary
is deliberate: the bridge is a decode-and-propagate theorem, not a proof that
the accumulator cannot overflow.

## Deliberate boundary

The current coefficient facts are not strong enough to imply safety. The
documented all-one pressure case already shows why: one odd-root ideal squared
magnitude is about `26561`, so three such `s1` slices reach about `79683`,
which is above the decoded signed-Q16 nonnegative ceiling `32768`.

So the accumulator contract must stay explicit until a sharper spectral
safe-trace theorem, a quantified bad-event argument, or a widened accumulator
implementation is introduced. This milestone therefore records the boundary
cleanly and keeps the safety premise visible.

## Verification

The proof artifacts are:

- `easycrypt/spec/KeygenM23SingularFFTAccumulatorBridge.ec`; and
- `easycrypt/refinement/TargetKeygenM23FirstAttemptAccumulator.ec`.

Both are part of `manifests/keygen-m23-matrix-proof-files.txt` and are checked
by `./scripts/verify-keygen-m23-matrix-proof.sh` with fresh `-no-eco`
compilation plus the existing proof-hole, authored-axiom, and debug-command
scans. No axiom was added. The safe-trace premise remains registered as
`OBL-FFT-SAFE-TRACE` rather than being hidden as an assumption.
