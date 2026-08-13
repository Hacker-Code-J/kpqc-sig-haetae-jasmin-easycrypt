# Post-freeze actual `avec` / paper `a,qj` report

## Verdict

`STOP-KG-AVEC-QJ — OBL-KG-SECURITY-EXPANDVECA-SEMANTICS`

The deterministic semantics of every terminating actual Mode-2 `avec`
expansion are proved and connected to the paper object `a`.  The paper term
`qj` is also defined and composed with the actual finalizer snapshot.  The
requested identification with the existing security-side object cannot be
proved, because that object has different semantics.

Consequently this run does **not** claim KG-1--KG-4 or
`A s = q j (mod 2q)`.

## Scope and frozen boundary

- Work branch: `post-freeze-kg-rq-haetae-bridge`.
- Frozen `main`/`origin/main`: `4bde1207e2a290952d491d5b41c4bd773081e3c4`.
- No frozen paper, PDF, reference extraction, NTT proof, security source,
  Verify, Sign, codec, packer, or public API file was changed.
- The proof concerns partial correctness of terminating executions only.  It
  makes no sampler distribution, uniformity, losslessness, or termination
  claim.

## Closed deterministic leaves

`post-freeze/KgActualAvecQjSemantics.ec` provides the exact Mode-2 stream
surface:

- `mode2_vector_nonce_row0` and `mode2_vector_nonce_row1`: row nonces are 515
  and 516.
- `mode2_vector_seed_byte` and `mode2_vector_nonce_bytes`: the SHAKE128 input
  is `seedbuf[0..31] || [3+row,2]`.
- `mode2_a_padding_bytes`: the framed input has domain byte 31 at offset 34
  and final padding byte 128 at offset 167.
- `mode2_a_xof_bytes_size` and `mode2_a_initial_xof_bytes_size`: each squeeze
  block contributes 168 bytes and the initial four blocks contribute 672.
- `mode2_a_candidate_le16` and `mode2_a_rejection_filter`: adjacent bytes are
  decoded little-endian and only candidates below 64513 are retained.
- `mode2_uniform_stream_parsed_coefficient`: every active stored word equals
  the corresponding accepted candidate.
- `mode2_paper_a_stored_without_reduction`: an accepted coefficient is stored
  unchanged; there is no post-acceptance modular reduction.
- `mode2_uniform_stream_paper_a_flat`: the two 256-coefficient array rows are
  the paper-level Mode-2 vector `a`.

The paper module basis vector is represented coefficientwise by

```text
j[row,coeff] = 1  iff row=0 and coeff=0
qj[row,coeff] = 64513 * j[row,coeff].
```

This distinction matters: the first entry of `j=(1,0)^T` is the ring identity
polynomial, not the polynomial whose every coefficient is one.  The
independent correction leaves are therefore:

- `paper_qj_row0_coeff0`: `+q` at row 0, coefficient 0;
- `paper_qj_row0_other`: zero at all other coefficients of row 0;
- `paper_qj_remaining_row`: zero throughout row 1.

`post-freeze/KgActualAvecQjComposition.ec` then proves:

- `mode2_sampler_facts_actual_paper_a`: the actual combined sampler facts
  imply the whole coefficientwise paper-`a` interpretation;
- `actual_snapshot_zero_adds_paper_qj`: the independent `qj` term composes
  with the already-proved snapshot mod-`2q` zero equation;
- `checked_mode2_parent_m23_finalize_actual_avec_qj`: one Hoare theorem over
  the actual checked sampler, `_kp_m23_matrix`, and finalizer path exports both
  results without assuming a desired sampler equality, KG-3/KG-4, or the final
  key equation.

## Exact minimum blocker

The current security model defines

```text
haetae_mode23_qj_vector md sd
  = public_rounding_vector_seed md sd
  = public_key_seed_polyveck md 401 sd.
```

This is a synthetic tagged arithmetic generator.  It is neither the actual
SHAKE128/rejection expansion nor the paper term `qj`.  The compiled leaves in
`post-freeze/KgActualAvecQjBlocker.ec` show, for every seed:

```text
security_named_qj[0][0] = 401
security_named_qj[1][0] = 403
paper_qj[0][0]          = 64513.
```

Thus `security_named_qj_is_not_paper_qj` proves the object-level mismatch
without any sampler or KG assumption.  An independent FIPS-202 trace for the
all-zero raw seed additionally gives:

```text
rho = f5977c8283546a63723bc31d2619124f
      11db4658643336741df81757d5ad3062
actual nonce-515 row0[0] = 44985
synthetic security row0[0] = 401.
```

The minimum repair leaf is therefore
`OBL-KG-SECURITY-EXPANDVECA-SEMANTICS`:

> Replace or refine the synthetic security `public_rounding_vector_seed`
> surface with the same SHAKE128, little-endian 16-bit parsing, `<64513`
> rejection, and 515/516 nonce schedule as the actual Mode-2 expansion; keep
> the paper `qj` basis correction as a separate mod-`2q` object; then prove
> the coefficientwise actual-array representation theorem.

This leaf is prior to KG-1/KG-3/KG-4.  Assuming the desired equality would
identify 44985 with 401 for the concrete trace and would be unsound.

## Why the final KG equation is not promoted

The existing NTT row-product, Rq-to-HAETAE dot-product bridge, and KG-2
snapshot remain reusable and unchanged.  The snapshot has been extended with
the correct paper `qj` term, but it is not relabeled as a width-6 matrix-vector
equation.  Such a promotion must first use a faithful security `a` object and
must separately package the full mod-`2q` matrix and secret.  The current
HAETAE algebra is modulo `q` and its Mode-2 vector width is four, whereas the
paper augmented key matrix has width `1+3+2=6`; in particular, its existing
operations cannot retain the integer `qj` correction.

## Verification commands

The three new EasyCrypt targets were freshly compiled with `-no-eco`, Z3,
and the repository include paths.  All three passed.  The deterministic
witness is checked with:

```sh
python3 haetae-topdown-easycrypt/post-freeze/check-kg-actual-avec-qj-trace.py
```

The aggregate frozen suite was rerun and terminated with:

```text
PASS baseline verification
PASS LaTeX research notes build
PASS read-only roots unchanged after verification
PASS paper-freeze scope and 82-target evidence audit
RESULT PASS authored-targets=82 cache=-no-eco
```

The frozen PDF `haetae-topdown-easycrypt/latex/main.pdf` retains SHA-256
`be935948028829556951863b44ceb2e6c5b2037820991b3a43a4b461b036e53d`.
The regenerated 82-target summary retains SHA-256
`08ef9639dc73d56dba42d02999d07897d29bc8e60aa100a648e9437fd64387ad`.
Local `main` and `origin/main` both remain at frozen commit
`4bde1207e2a290952d491d5b41c4bd773081e3c4`.
