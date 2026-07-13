# Reproducibility Logs

These logs record the checker and assembly-comparison evidence used by
`paper/jasmin_safety_ct.tex` and `paper/jasmin_safety_ct_ko.tex`.

All commands were run from the repository root.

| Log | Command | Expected result |
| --- | --- | --- |
| `jasminc-version.log` | `jasminc -version` | Jasmin compiler version. |
| `git-revision.log` | `git rev-parse --short HEAD` | Artifact source revision. |
| `jasmin-checksafety.log` | `jasminc -checksafety -o /tmp/hpoly-safe.s jasmin/hpoly.jazz` | `No Safety Violation` for `poly_ntt_jazz`, `poly_invntt_jazz`, and `poly_basemul_jazz`. |
| `jasmin-ct.log` | `jasmin-ct jasmin/hpoly.jazz` | Empty output with exit status 0. |
| `jasmin-ct-speculative.log` | `jasmin-ct --speculative jasmin/hpoly.jazz` | Exported wrappers typed from transient pointers to public pointers over secret values. |
| `jasmin-compile.log` | `jasminc jasmin/hpoly.jazz -o /tmp/hpoly-after.s` | Empty output with exit status 0. |
| `assembly-sha256.log` | `sha256sum hpoly.s /tmp/hpoly-after.s` | Matching hashes. |
| `assembly-diff.log` | `diff -u hpoly.s /tmp/hpoly-after.s` | Empty output. |
