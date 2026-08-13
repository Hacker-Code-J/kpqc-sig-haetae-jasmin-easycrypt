# RESUME-VERIFY-MATRIX-CRT-POSTFREEZE closeout report

## Decision

**STOP-VERIFY-MATRIX-CRT-POSTFREEZE — actual count=4 forward-NTT representation bridge.**

The requested combined theorem

```text
verify_matrix_crt_mode2_fromcrt_freeze_exact
```

is still unproved. The actual CRT/from-CRT/freeze word-semantics lane now has
a fresh-compiled theorem, but the matrix lane still stops at the first actual
`count = 4` forward-NTT representation obligation. No KeyGen-only
three-column theorem is promoted to the Verify four-column claim.

## Verified isolated post-freeze surfaces

Both files remain outside the frozen 82-target manifest.

### `post-freeze/VerifyMatrixCrtPostFreeze.ec`

This file:

1. defines `ActualVerifyMatrixNttAccMode2.run`, which calls the actual
   `VerifyCoreTarget.M` helpers in order:
   `_polyvec_ntt(count = 4)`,
   `_polymat_pointwise_acc(rows = 2, cols = 4)`, and
   `_polyvec_invntt(count = 2)`;
2. proves procedure equivalence between the Verify and parent extracted
   `_polyvec_ntt` bodies;
3. proves the corresponding `_polymat_pointwise_acc` equivalence; and
4. proves the corresponding `_polyvec_invntt` equivalence.

These are actual-call and procedure-identity facts. They do not establish the
missing representation, arithmetic-bound, or combined correctness theorem.

### `post-freeze/VerifyCrtFreezeMode2PostFreeze.ec`

This file now fresh-compiles the following actual word-semantics facts:

- `freeze2q_word_correct`, matching the extracted `Verify.__freeze2q` body;
- `polyvec_freeze2q_mode2_word_exact`, covering the 512 active words and
  preserving the coefficient tail from word 512 through word 2047;
- `polyveck_poly_fromcrt_mode2_word_exact`, covering the two mode-2 rows,
  including the first-row xor/parity rule, second-row high-parity rule, and
  the same tail frame; and
- `verify_crt_freeze_mode2_word_exact`, composing the actual from-CRT and
  freeze calls into `crt_freeze_prefix` over all 512 active words while
  preserving the inactive tail.

This proves the stated extracted word formulas and frame properties. It does
not by itself prove the matrix NTT/pointwise/inverse-NTT lane or the requested
combined matrix/CRT theorem.

## Exact first unresolved actual procedural leaf

The first unresolved child of

```text
verify_matrix_ntt_acc_mode2_cols4_correct
```

is the representation bridge for the actual call

```text
Verify._polyvec_ntt (z1p, W64.of_int 4)
```

inside `ActualVerifyMatrixNttAccMode2.run`.

The imported theorem
`TargetKeygenM23WideNTT.parent_polyvec_ntt_mode2_correct` exports only the
KeyGen mode-2 `count = 3` result. There is still no compiled theorem taking
the actual Verify `count = 4` return to the required four-slice
`vector_forward_repr` and tail-frame facts.

After that bridge, the next missing leaf is the actual
`_polymat_pointwise_acc(rows = 2, cols = 4)` semantic-and-bound theorem. Its
fourth column requires a new tight `bw18` accumulation result; the existing
`TargetKeygenM23Pointwise.polymat_pointwise_mode2_repr_bound18_frame` covers
only three columns.

## Verification evidence

- `VerifyMatrixCrtPostFreeze.ec`: standalone fresh
  `easycrypt compile -script -no-eco` completed with exit code 0 against the
  regenerated Verify extract plus the explicit parent/spec/refinement/NTT
  include surface.
- `VerifyCrtFreezeMode2PostFreeze.ec`: standalone fresh
  `easycrypt compile -script -no-eco` completed with exit code 0 against the
  regenerated Verify extract.
- Full frozen verification ran from an isolated copy of the current source to
  avoid concurrent writers to the workspace summary, and completed with
  `RESULT PASS authored-targets=82 cache=-no-eco`.
- Manifest proof-hole scan passed, and both isolated post-freeze files passed
  direct proof-hole, authored-axiom, and debug/temporary-declaration scans.
- The paper-freeze scope and 82-target evidence audit passed.
- `git diff --check` passed.

## Boundaries preserved

- `c38b3fb` remains the correctness boundary for the earlier
  `GO-KG-FAITHFUL-AUGMENTED` lane.
- The frozen 82-target manifest is unchanged.
- No existing security artifact, `ExpandVecA` definition, frozen paper source,
  or manifest entry was modified.
- The pre-existing dirty `theory-guide` and `algebraist-guide` changes were
  left untouched and are excluded from this closeout commit.

## Scope honesty

This closeout proves `verify_crt_freeze_mode2_word_exact` at its stated word
and tail-frame scope. It does **not** claim:

- `verify_matrix_ntt_acc_mode2_cols4_correct`;
- `verify_matrix_crt_mode2_fromcrt_freeze_exact`;
- paper `(V-3)` / `(V-4)`;
- any reject/norm success premise; or
- the separate challenge leaf.

The final result is therefore:

**STOP-VERIFY-MATRIX-CRT-POSTFREEZE — actual count=4 forward-NTT representation bridge.**
