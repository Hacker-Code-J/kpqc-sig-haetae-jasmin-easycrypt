# Target mode-2 FFT accumulator probability schema

## Scope

This milestone gives the conservative five-slice accumulator headroom event an
axiom-free probability interface. It works over an arbitrary distribution on
the two input arrays, decomposes the global event into finite local families,
and lifts the resulting bound to the immutable first-attempt trace. It does
not define the key-generation distribution or prove numeric spectral tails.

The generic theory is
`easycrypt/spec/KeygenM23SingularFFTAccumulatorProbability.ec`. The target
projection is
`easycrypt/refinement/TargetKeygenM23FirstAttemptAccumulatorProbability.ec`.

## Finite event decomposition

The global event can fail through two finite families:

- six processed-prefix endpoints, `0` through `5`, at each of 256
  coordinates, for `6 * 256 = 1536` prefix sites; and
- five FFT slots, `0` through `4`, at each of 256 coordinates, for
  `5 * 256 = 1280` coordinate sites.

Each prefix site is split into the exact negations of its two sufficient
margins:

- lower failure: folded ideal energy is below the folded error budget; and
- upper failure: folded ideal energy plus error reaches the decoded signed-Q16
  limit.

Each FFT-coordinate site is split into real and imaginary failures, where the
absolute ideal coordinate plus the checked endpoint error exceeds the decoded
cap `127`.

`mode2_accumulator_headroom_bad_event_cover` proves that every global headroom
failure belongs to at least one of these finite families. The proof counts the
site sets inside EasyCrypt; the coefficients are not handwritten estimates.

## Parameterized probability theorem

For any distribution `d` on the two accumulator input arrays, the main theorem
proves

```text
mu d headroom_bad
  <= 1536 * (delta_lower + delta_upper)
     + 1280 * (delta_real + delta_imag)
```

provided every valid site has the corresponding marginal measure bound. The
proof first applies the finite union bound across sites, then the two-event
union bound within each site. It assumes no independence between slots,
coordinates, prefixes, or the two arrays.

The four deltas remain theorem parameters. In particular, choosing numeric
values requires a checked law for the actual key-generation samples and
spectral tail results for their ideal odd-root FFT outputs.

## First-attempt projection and safety domination

The target theory projects an arbitrary distribution on `first_attempt_trace`
to `(s1, final_s2)` with `dmap`. It proves exact equality between the measure
of `first_attempt_trace_accumulator_headroom_bad` and the generic event under
that projected distribution, then exports the same split union bound.

Two measure-domination theorems connect this analytic event to the already
checked deterministic consequences:

- within `first_attempt_snapshot_facts`, failure of the exact accumulator-safe
  trace has measure at most the headroom-bad measure; and
- for every valid coordinate, failure of the decoded accumulator energy-error
  endpoint has measure at most the same headroom-bad measure.

These are one-way safety consequences. Headroom failure remains a conservative
sufficient bad event and is not claimed to be equivalent to actual overflow.

## Remaining numeric boundary

The extracted keygen sampler proofs currently expose deterministic
finite-stream, range, frame, and progress-certificate properties, but no law
for the five first-attempt slices and no tail theorem for their ideal FFT
energies. The signing rejection and random-oracle losses elsewhere in the
security development do not provide that missing bridge.

The next probability milestone is therefore to:

1. define and prove the actual first-attempt keygen distribution;
2. instantiate the four local marginal tail bounds;
3. lift the event accounting through later retry attempts; and
4. connect the safe energy endpoint to the tie-sensitive score, guard,
   acceptance, and retry termination.

## Verification

Both theories are entries in
`manifests/keygen-m23-matrix-proof-files.txt` and are checked by:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-m23-matrix-proof.sh
```

The gate compiles every manifest entry from source with `-no-eco` and runs the
proof-hole, authored-axiom, and debug-command scans. No project-authored axiom
or numeric probability assumption is added.
