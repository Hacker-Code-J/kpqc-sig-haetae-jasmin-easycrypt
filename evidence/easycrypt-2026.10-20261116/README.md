# HAETAE: EasyCrypt 2026.10 scoped replay

This record preserves a successful **isolated-snapshot** replay completed on
2026-11-16 using EasyCrypt `r2026.10` (`859766e50e936fb9e420fb6fb1ad8824ffb8d83e`).
The tested source state starts from `34cafa425e443556da848d4a31cf142732426c40` plus the proof-only
[patch](proof-port.patch). The corresponding proof bytes have now been applied
to this repository. The base commit is not presented as a commit containing
those later changes, and applying the patch is not a new whole-project replay.

| Recorded check | Count |
| --- | ---: |
| Fresh primary proof files | 14 PASS |
| Intentional unfinished/false-proof rejection controls | 4 PASS |
| Existing gate regression tests | 10 PASS |
| Proof-body files changed | 1 |

The theorem statements, assumptions, definitions, implementations and exported
numerical bounds are unchanged. The ports discharge the new nonnegativity
obligations using existing lemmas. The Gaussian retry mass and losslessness proofs are the only modified sites.

## Portable evidence check

From the repository root:

```sh
python3 evidence/easycrypt-2026.10-20261116/check.py
```

The check uses only this checkout. It needs neither the author's home directory
nor the original replay folder, and does not invoke EasyCrypt. It checks the
pinned index, payload/log hashes, current proof-source hashes, target counts,
intended rejection diagnostics and unchanged non-proof text in changed sources.
The exact EOF wrappers and gate test used in the recorded run are retained under `recorded-verifiers/`.
Run `python3 evidence/easycrypt-2026.10-20261116/test_check.py` from the repository root to exercise log, index, proof-source and escaping-symlink mutations in temporary copies.

The digest anchor in `check.py` is an integrity guard, not an external digital
signature; changes to both checker and evidence require normal source review.

[index.json](index.json) contains source-relative bindings and exact recorded
commands, tool hashes, limits, exit codes, resource measurements and copied log
paths. The copied raw logs retain their original bytes and host paths; these
paths are historical observations, not dependencies of this check.
The existing historical evidence and release pins have not been overwritten.

## Proof-port and import boundary

Original changed sources are preserved as `before/<repository-relative-path>`.
The checker compares their non-proof text with the current files.
The local require graph had 168 imported-only dependencies; their bodies were not all checked as primary files.
The final 14-target round used one frozen source snapshot.

This does not establish a fresh proof of every imported theorem, a fresh Jasmin
extraction, full-project reproduction, new cryptographic assumptions, or a
tighter numerical security/failure bound. The original source/result inventories
remain separately preserved; their digest is recorded as `origin_result_sha256`.

## Performance measurements

[benchmark/results.json](benchmark/results.json) preserves this project's
samples and measured medians. Each version/case ran three times with alternating
order, identical source/solver limits, no `.eco` caches and a shared execution
lock. Lock-wait time is excluded. The comparison includes each release's
standard library; import cases do not replay imported proof bodies. Filesystem
caches and other host workloads were not controlled. These are local
measurements, not a statistical performance guarantee.
