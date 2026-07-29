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
to realize; it does not yet establish that machine correspondence.

## Deliberate boundary

This milestone does not yet prove that:

- an extracted Q16 coordinate is the rounded coordinate of `ideal_root j`;
- the exact radix-2 array schedule and bit reversal compute the ideal DFT;
- machine multiplications stay in their signed ranges;
- accumulated fixed-point error stays within a stated bound; or
- the machine rejection guard agrees with the ideal guard.

In particular, the extracted table cannot itself serve as the exact root:
rounding makes its nontrivial entries only approximately unit norm.  The
existing table certificate and this exact construction are intentionally
separate inputs to the next rounding proof.

## Next dependency

The remaining analytic chain is:

1. prove the ideal radix-2 and bit-reversal schedule identity;
2. certify every extracted root coordinate as the intended Q16 rounding, with
   a coordinate error bound;
3. lift the local integer decoders through the eight-stage safe trace and all
   five squared-magnitude passes;
4. propagate error through accumulation, selection, and the retained
   multiplicity-sensitive finish rule; and
5. relate acceptance only outside the resulting error band.

## Verification

Run the complete authored gate:

```sh
cd haetae-ref-easycrypt
./scripts/verify-keygen-m23-matrix-proof.sh
```

The gate compiles the theory from source with `-no-eco` and rejects proof
holes, project-authored axiom declarations, and leftover debug commands.
