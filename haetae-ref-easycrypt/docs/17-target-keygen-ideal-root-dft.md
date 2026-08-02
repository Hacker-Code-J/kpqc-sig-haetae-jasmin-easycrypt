# Target mode-2 ideal root and odd-root DFT

## Scope

This milestone constructs the ideal complex root needed to interpret the
mode-2 singular-value FFT.  It stays above the machine-word layer: the root is
an exact pair of EasyCrypt reals, while the extracted implementation table
continues to contain rounded Q16 integers.

`easycrypt/spec/KeygenM23IdealRootDFT.ec` adds no project-authored axiom.  It
uses the installed `RealExp.sqrt`, whose square, sign, and monotonicity laws
are proved in the standard EasyCrypt theories, and instantiates the standard
commutative-ring power theory for the transparent complex representation.
This is not a foundations claim: the installed real-number theories remain
part of the trusted mathematical library.

## Constructive root

The reference table is documented as the Q16 rounding of
`exp(-i*pi*k/256)`.  The proof therefore selects the lower-half-plane branch.
For a unit complex value `z`, it defines

```text
chalf_neg(z) =
  (sqrt((1 + Re(z))/2), -sqrt((1 - Re(z))/2)).
```

The checked `chalf_neg_square` lemma proves that this value squares to `z`
under the explicit lower-unit invariant.  `chalf_neg_lower_unit` proves that
the invariant is preserved.  Starting at `-i` and applying this construction
seven times yields an explicit `omega512`.

The exported power anchors identify the selected orientation:

```text
omega512^128 = -i
omega512^256 = -1
omega512^512 = 1
```

The theory packages the last two anchors as the checked power-of-two
primitivity criterion: `omega512^512 = 1` while
`omega512^256 <> 1`.  It deliberately exports that precise dyadic criterion
rather than claiming a separately formalized universal minimal-order
predicate.

## Ideal transform surface

The same theory defines:

- `ideal_root j = omega512^j`;
- the 256th root used by the radix-2 stages as `omega512^2`;
- the odd evaluation root `omega512^(2*k+1)`;
- an unnormalised 256-point complex DFT;
- the coefficient twist by `omega512^j`; and
- the unnormalised odd-root DFT of a complex-valued input function.

The checked twist identity reduces each odd-root kernel

```text
omega512^((2*k+1)*j)
```

to the initialization twist `omega512^j` followed by the ordinary 256-point
DFT kernel `(omega512^2)^(k*j)`.  The exported `odd_dft256_twist` theorem is
stated for `0 <= k`; its finite sum supplies `0 <= j < 256`.  This establishes
the ideal algebraic factorization that the C and Jasmin schedule is intended
to realize; it does not establish that machine correspondence.

## Deliberate boundary

The follow-on `KeygenM23IdealFFTSchedule` theory now proves that a pure
exact-complex, bit-reversed, eight-stage radix-2 schedule computes `dft256`,
and that its twisted-input form computes `odd_dft256`. The subsequent
root-table certificate now proves that every extracted coordinate is the
unique nearest Q16 encoding of the corresponding `ideal_root j` coordinate.
The subsequent initialization bridge now proves the decoded target
initialization and its error against the exact bit-reversed twisted input.
The subsequent one-butterfly bridge proves exact stores, decoded outputs,
frames, and local Q16 error for one safe kernel. The subsequent inner-prefix
bridge composes its exact rounded semantics on each evolving pre-step state.
None of these theories yet proves that the rounded block or stage folds
implement the ideal schedule.

The remaining boundary is that no theorem yet proves:

- the complete extracted or exact-word machine evaluator is related to
  `ideal_fft256` beyond initialization and the rounded inner prefix;
- all scheduled rounded butterfly multiplications stay in their signed ranges;
- accumulated fixed-point error stays within a stated bound; or
- the machine rejection guard agrees with the ideal guard.

In particular, the extracted table cannot itself serve as the exact root:
rounding makes its nontrivial entries only approximately unit norm. The new
certificate relates the table to that root by strict coordinate error rather
than asserting exact complex equality.

## Next dependency

The remaining analytic chain is:

1. discharge the explicit safety contract on the now-composed eight-round
   machine trace and connect it to the ideal schedule through all five
   squared-magnitude passes;
2. propagate the certified coordinate and local rounding errors through the
   FFT, accumulation, selection, and the retained
   multiplicity-sensitive finish rule; and
3. relate acceptance only outside the resulting error band.

The exact schedule proof is detailed in
[`18-target-keygen-ideal-fft-schedule.md`](18-target-keygen-ideal-fft-schedule.md),
and the extracted-table certificate is detailed in
[`19-target-keygen-root-table-rounding.md`](19-target-keygen-root-table-rounding.md).
The decoded initialization milestone is detailed in
[`20-target-keygen-fft-initialization-bridge.md`](20-target-keygen-fft-initialization-bridge.md).
The local butterfly milestone is detailed in
[`21-target-keygen-fft-butterfly-bridge.md`](21-target-keygen-fft-butterfly-bridge.md).
The exact evolving-state inner-prefix milestone is detailed in
[`22-target-keygen-fft-k-prefix-bridge.md`](22-target-keygen-fft-k-prefix-bridge.md).
The exact evolving-state block-prefix milestone is detailed in
[`23-target-keygen-fft-block-prefix-bridge.md`](23-target-keygen-fft-block-prefix-bridge.md).

## Verification

Run the complete authored gate:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-m23-matrix-proof.sh
```

The gate compiles the theory from source with `-no-eco` and rejects proof
holes, project-authored axiom declarations, and leftover debug commands.
