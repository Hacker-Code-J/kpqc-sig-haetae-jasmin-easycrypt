# Hyperball numerical boundary

The implementation computes a **64-bit modular sum of squared signed 32-bit
coefficients**. If the mathematical sum is `N`, `_polyfixveclk_sqnorm2_2048`
returns `N mod 2^64`, and `_sf_scale_and_check` accepts when that residue is at
most the mode's bound. See `generated/api/ApiTarget.ec`, procedures
`_polyfixveclk_sqnorm2_2048` and `_sf_scale_and_check`.

The geometric conclusion `N <= bound` is conditional on `N < 2^64`. Existing
Gaussian per-event ranges alone do not supply that condition or establish a
convergence domain for the initial estimate and six Newton updates. The pinned C
`src/fixpoint.c:119-121` explicitly notes that the first iterate may be negative.
Accepted zero candidates are also possible, so positivity of the denominator
requires a separate argument. Claims about real-valued normalization additionally
need rounding/error bounds and proofs that intermediate arithmetic and conversion
to signed 32-bit coefficients preserve the intended integer values.

## Deterministic finite witnesses

The replay prescribes candidate bytes and zero sign bits. Each candidate is
accepted by the C and Jasmin sigma samplers. Repeating it for `count + 2`
accepted events models Hyperball's two 257-event streams and its remaining
256-event streams: two values contribute squares but are not stored. The
resulting stored vector contains `count` copies of the displayed coefficient.

**These are abstract candidate-sequence counterexamples to a deduction from
per-event ranges and mode constants alone. No SHAKE seed producing these
streams is supplied or claimed, and the replay is not an exploit demonstration.**

| Mode | Stored count | Signed coefficient | Mathematical squared norm `N` | `N mod 2^64` | Acceptance bound |
| --- | ---: | ---: | ---: | ---: | ---: |
| 2 | 1536 | -1704795102 | 4464117257937700460544 | 5192099988969472 | 6505809026482176 |
| 3 | 2304 | -334802028 | 258260884883511054336 | 6467851577331712 | 22510896139993088 |
| 5 | 2816 | -632138900 | 1125272442323279360000 | 21053826996711424 | 33503371683954688 |

The respective quotients by `2^64` are 242, 14, and 61. Every residue passes
the word comparison while its mathematical sum exceeds the bound.

The fixed 26-byte candidates, in input byte order, are:

```text
mode 2: f02b9beab2fa80e32cff07010000000000fa0c64c17e9d051d68
mode 3: 85666c58d6ffffffffff07010000000000e682480d5e84d3bc6c
mode 5: 0137e5ab1a741e4c3bf00701000000000030437515a2b15216a0
```

`tests/hyperball-norm-boundary.py` records all mode constants and exact
intermediate limbs. Its test-only C probe includes the pinned reference sources;
it does not change production/reference files or replace the library's RNG.
The replay checks candidate acceptance, sample/square values, rounded halving,
the first Newton subtraction, the final Newton result, scale, rounded
coefficient, split output vectors, modular acceptance, and the mathematical
integer sum. These checks compare the C reference, fixed expected values, and
the corresponding compiled Jasmin library. No random search is performed.

`proofs/HyperballNormBoundary.ec` separately proves the three guarded integer
sum/residue/bound facts. It introduces no assumptions about SHAKE or sampling,
and is not a formal proof of reachability or of the whole numerical replay.

## Subsequent formal helper replay

The [actual-helper witness proof](hyperball-actual-witnesses.md) now derives
these outcomes from the prescribed candidate bytes in EasyCrypt. It calls the
actual finite consumer for requests257,257,256,..., includes both unstored
squares, and composes actual half/Newton/scaling/norm calls. Its final theorem
has no expected sample, square, scale or coefficient premise. It proves
accepted word1 while the mathematical norm of the returned arrays exceeds
the bound for modes2/3/5.

This is a deterministic supplied-buffer experiment. The actual finite-consumer
calls receive6656 or6682 candidate bytes, rather than reproducing the seeded
controller's initial6632-byte candidate region and refill schedule. No producing
SHAKE seed, full seeded-Hyperball reachability or formal C execution is claimed.
The original `HyperballNormBoundary.ec` remains the smaller arithmetic result
described above; the new replay supplies the additional source linkage.

## Reproduction

From the repository root:

```sh
python3 haetae-1.2.0-easycrypt/tests/hyperball-norm-boundary.py
```

The replay uses Python's standard library and the existing `cc`, `make`, and
Jasmin toolchain on the project's supported x86-64 platform. It checks the
existing per-mode shared-library build targets serially, builds fresh C probes
in a temporary directory, and prints each Jasmin library's SHA-256. `CC` may
select another compatible installed C compiler. Temporary probes are removed
when the replay finishes.

For a fresh EasyCrypt check, from `haetae-1.2.0-easycrypt/`:

```sh
bash scripts/verify-one.sh proofs/HyperballNormBoundary.ec
```

The existing wrapper uses `-no-eco`, enables proof checking, and appends a checked
EOF declaration so an unfinished proof cannot pass merely by reaching EOF.
