# Verification Status

Generated artifact:

- `Hpoly_extract.ec` was regenerated from `../jasmin/hpoly.jazz` using:

```sh
jasmin2ec --array-model=barray --output-array=easycrypt-ct \
  -o easycrypt-ct/Hpoly_extract.ec jasmin/hpoly.jazz
```

Current results:

- `./scripts/regenerate-extract.sh` regenerates `Hpoly_extract.ec` from the
  full-safe constant-time Jasmin source.
- `./scripts/check-functional-support.sh` compiles `FunctionalSupport.ec`,
  which imports `NTTFullAlgebra.ec` and `Hpoly_extract.ec`, using `-no-eco`.
- `Hpoly_loop.ec` compiles as the proof-only direct-loop model using the CT
  extraction's constants and `__fqmul`.
- `RefJasminNTTLoop.ec` compiles the existing direct-loop functional
  correctness proof against `Hpoly_loop.ec`.
- `CTLoopEquiv.ec` compiles the machine-checked bridge from the helperized
  full-safe constant-time extraction to the proof-only direct-loop model.
- `NTTEndToEnd.ec` compiles the final machine-checked functional correctness
  theorem for the extracted CT public wrappers.

Preserved historical boundary:

```text
[critical] [RefJasminNTT.ec: line 1766 (34-37)] unknown variable or constant: `len'
```

Boundary command:

```sh
easycrypt compile -no-eco RefJasminNTT.ec -I .
```

Reason:

The existing refinement proof was written against the original direct-loop
Jasmin extraction.  The full-safe implementation replaces the dynamic
`len/start/zetasctr` loop in the extracted `_poly_ntt` and `_poly_invntt`
procedures with a sequence of fixed stage helper calls.  `RefJasminNTT.ec` is
kept unchanged to document that old proof shape.  The checked proof path is now
`RefJasminNTTLoop.ec` plus `CTLoopEquiv.ec` plus `NTTEndToEnd.ec`.

Full proof command:

```sh
cd easycrypt-ct
./scripts/check-full-functional-correctness.sh
```
