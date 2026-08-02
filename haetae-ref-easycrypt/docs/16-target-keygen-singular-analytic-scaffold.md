# Target mode-2 singular analytic scaffold

## Scope

This milestone prepares the exact machine-word singular evaluator for a later
real/complex error proof.  It adds checked local decoding, a transparent
complex arithmetic layer, finite facts about the extracted tables, and a
guard-crossing tie regression.  It does not yet prove that the machine FFT is
an odd-root DFT or that an actual execution satisfies every numerical safety
premise.

## Checked proof surface

`easycrypt/spec/KeygenM23ComplexReal.ec` represents a complex value
transparently as a pair of EasyCrypt reals.  It proves the coordinate,
addition, subtraction, multiplication, conjugation, squared-norm, scaling,
and coordinatewise perturbation laws needed for an FFT error recurrence.
The theory adds no project-authored axiom declaration.  It relies on the
installed standard real-number theories, so it is not a construction of the
reals from first principles.

`easycrypt/spec/KeygenM23FFTTableCertificate.ec` proves two finite facts about
the constants in the actual zero-drift parent extraction:

- `jfft_brv8_exact` identifies every one of the 256 extracted `W16` entries
  with `bsrev 8 i`; and
- `jfft_roots_signed_bound` proves that all 512 extracted signed root
  coordinates lie in `[-65536, 65536]`.

These are structural and range certificates.  They do not identify a root
coordinate with the rounding of an ideal primitive-root coordinate.

`easycrypt/spec/KeygenM23SingularIntegerSemantics.ec` proves local signed
integer decoders under the explicit predicates from
`KeygenM23SingularBoundary`:

- Q16 multiplication and initialization multiplication;
- the two complex-product terms and four scalar butterfly outputs;
- squared magnitude and one accumulator update; and
- the untouched-entry frame for that update.

The butterfly result is a local scalar-kernel theorem, not yet a theorem about
the complete array-indexed stage.

`easycrypt/spec/KeygenM23SingularTieRegression.ec` proves a finish-stage
regression with five already-selected equal entries:

```text
implementation multiplicity-sensitive score = 375000
paper fixed-weight score                    = 800000
375000 <= mode-2 bound 611098 < 800000
```

The regression proves that the policies can produce different guard outcomes.
It explicitly makes no reachability claim about the FFT or selector.

## Compatibility decision

The reference C, Jasmin, and exact EasyCrypt evaluator all give the remainder
weight to every selected value equal to the retained minimum.  The current
proof therefore preserves this deployed multiplicity-sensitive rule.

An unretained, one-off diagnostic over the retained 100-case KAT corpora
observed no selected-minimum tie in modes 2, 3, or 5.  A disposable mode-2
build in that diagnostic assigned the remainder only once and produced the
same 100-case response file, with SHA-256
`8414c29dc5d24b548b748dfc4208796619877a7e2e7605da978a8875fa36951b`.
The retained case counts and current file hash are reproducible; the
diagnostic itself is not retained.  It suggests that those vectors do not
distinguish the policies, but it does not show that a tie is unreachable.  If
a guard-changing tie is reachable, changing the source rule may change the
retry counter and resulting public/secret key.  Such a change needs an
explicit algorithm-version decision and refreshed compatibility vectors
rather than an incidental proof patch.

## Remaining analytic chain

`KeygenM23IdealRootDFT` constructs the lower-half-plane 512th root, checks its
dyadic primitivity criterion, defines the ideal odd-root DFT, and checks the
algebraic coefficient-twist identity. `KeygenM23IdealFFTSchedule` now closes
the next ideal dependency: its bit-reversed eight-stage exact-complex schedule
computes `dft256`, and its twisted-input form computes `odd_dft256`.
`KeygenM23RootGeneratorCertificate`, `KeygenM23RootTableRounding`, and
`KeygenM23RootTableTargetBridge` now close the table dependency: every
extracted root coordinate is the unique nearest Q16 encoding of the
corresponding exact `ideal_root j` coordinate, with strict error below
`1/131072`. `KeygenM23SingularFFTInitBridge` now closes the complete decoded
initialization permutation, its signed-product safety for coefficient
magnitude at most two, and its `1/65536` whole-vector ideal-input error. The
follow-on `KeygenM23SingularFFTButterflyBridge` closes one rounded kernel:
four exact target stores, both exact decoded destinations under the named
safety predicate, every other cell framed, and `1/65536` local arithmetic
error against the decoded-root complex butterfly. The subsequent
`KeygenM23SingularFFTKPrefixBridge` composes those exact destination and frame
facts through any valid inner prefix on the rounded evolving machine state.
`KeygenM23SingularFFTBlockPrefixBridge` then composes complete inner loops
through any valid block prefix on the exact evolving pre-block states.
`KeygenM23SingularFFTStageBridge` closes the exact owner-block endpoint for
each reachable complete stage. That stage endpoint is still not identified
with the ideal transform.

The strongest sound next correspondence has the following dependency order:

1. discharge the explicit safety contract on the now-composed eight-round
   machine trace and connect it to the ideal schedule through all five
   squared-magnitude passes;
2. propagate the certified coordinate and local multiplication errors through
   the FFT, accumulation, selection, and the current multiplicity-sensitive
   finish rule; and
3. relate acceptance only outside the resulting numerical error band.

The certificate construction and target endpoint are detailed in
[`19-target-keygen-root-table-rounding.md`](19-target-keygen-root-table-rounding.md).
The decoded initialization endpoint is detailed in
[`20-target-keygen-fft-initialization-bridge.md`](20-target-keygen-fft-initialization-bridge.md).
The decoded one-butterfly endpoint is detailed in
[`21-target-keygen-fft-butterfly-bridge.md`](21-target-keygen-fft-butterfly-bridge.md).
The exact evolving-state inner-prefix endpoint is detailed in
[`22-target-keygen-fft-k-prefix-bridge.md`](22-target-keygen-fft-k-prefix-bridge.md).
The exact evolving-state block-prefix endpoint is detailed in
[`23-target-keygen-fft-block-prefix-bridge.md`](23-target-keygen-fft-block-prefix-bridge.md).

Coefficient bounds alone cannot prove the squared-magnitude accumulators safe:
the numerical boundary already gives a valid high-energy example.  A complete
theorem therefore needs a proved spectral safe-trace condition, a quantified
unsafe-trace event, or wider implementation arithmetic.  Acceptance after
wrapped arithmetic cannot be used to justify the missing premises
retroactively.

## Verification

The complete authored gate is:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-m23-matrix-proof.sh
```

The gate compiles every listed theory from source with `-no-eco` after source,
extraction-drift, and imported-support checks, then rejects proof holes,
project-authored axiom declarations, and leftover debug commands.
