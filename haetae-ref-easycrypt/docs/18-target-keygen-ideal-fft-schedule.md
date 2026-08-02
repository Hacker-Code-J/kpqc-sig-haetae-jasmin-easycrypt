# Target mode-2 ideal FFT schedule

## Scope

This milestone proves that a pure exact-complex, bit-reversed, eight-stage
radix-2 schedule computes the 256-point DFT defined in
`KeygenM23IdealRootDFT`. Applying the same schedule to the checked coefficient
twist computes the corresponding odd-root DFT.

`easycrypt/spec/KeygenM23IdealFFTSchedule.ec` stays entirely above the
fixed-point machine layer. Its values are pairs of EasyCrypt reals, its
twiddles are exact powers of the constructed `omega512`, and its additions and
multiplications do not round or wrap.

## Checked schedule

The theory defines `ideal_bitrev8` from `bsrev 8` and models each radix-2
round with the pointwise operator `ideal_stage`. At round `s`, the butterfly
half-width is `2^s` and the twiddle is

```text
ideal_root (2^(8-s) * k).
```

Thus the ideal operator uses the index geometry intended by the extracted
eight-round schedule without importing its rounded Q16 root coordinates or
word arithmetic.

The proof organizes the calculation through `partial_dft`. Its main invariant
states that, after `s` rounds, every length-`2^s` block contains the
corresponding partial transform of the bit-reversed input. The checked
low-half and high-half split lemmas give exactly the addition and subtraction
branches of one butterfly round. `ideal_stage_spec_step` lifts those lemmas
from one block to the complete pointwise stage, and
`ideal_schedule_prefix_stage_spec` iterates the invariant through all eight
rounds.

At length 256, `partial_dft256E` uses the permutation and involution properties
of `bsrev 8` to reindex the final sum into `dft256`. The exported endpoint is:

```text
ideal_fft256_correct:
  0 <= k < 256 ->
  ideal_fft256 input k = dft256 input k
```

The theorem is for the unnormalised exact-complex transform.

## Odd-root endpoint

`KeygenM23IdealRootDFT` previously proved that twisting coefficient `j` by
`omega512^j` converts the ordinary DFT kernel into the odd-root kernel. The new
schedule theorem composes directly with that identity:

```text
ideal_odd_fft256_correct:
  0 <= k < 256 ->
  ideal_fft256 (twist256 input) k = odd_dft256 input k
```

This closes the ideal algebraic schedule dependency. It does not close the
machine correspondence. A separate follow-on certificate now closes the
extracted-root-coordinate rounding dependency.

## Deliberate boundary

This milestone does not prove that:

- the complete `KeygenM23SingularFFTSpec` or extracted Jasmin evaluator is
  related to `ideal_fft256` beyond the separately proved initialization and
  rounded inner-prefix endpoints;
- every scheduled rounded butterfly, squared magnitude, or accumulator stays
  within its signed range;
- the eight rounded stages have a stated global error bound; or
- the machine score or rejection guard agrees with an ideal score or guard.

In particular, exact equality between the rounded fixed-point evaluator and
`dft256` is not asserted. The future bridge must relate them with explicit
rounding, safety, and error predicates.

`KeygenM23RootGeneratorCertificate`, `KeygenM23RootTableRounding`, and
`KeygenM23RootTableTargetBridge` now prove that every extracted signed
coordinate is the unique nearest Q16 encoding of `ideal_root j`, with strict
error below `1/131072`. That table theorem supplies the twiddle-error premise
for the future machine bridge; it is not itself an array-level FFT theorem.

## Next dependency

The remaining analytic chain is:

1. discharge the explicit safety contract on the now-composed eight-stage
   machine trace and connect it to the ideal schedule through all five
   squared-magnitude passes;
2. propagate the certified root-coordinate and local multiplication errors
   from that safe trace to
   `ideal_fft256`;
3. carry the error through accumulation, selection, and the retained
   multiplicity-sensitive finish rule; and
4. relate the machine and ideal rejection decisions only outside the resulting
   error band.

The root-table milestone is detailed in
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
