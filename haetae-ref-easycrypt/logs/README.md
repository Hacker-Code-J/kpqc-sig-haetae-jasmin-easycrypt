# Verification Logs

Project-specific extraction and proof scripts write their verification logs
here. Existing baseline scripts retain their logs in:

- `../../haetae-security/provable-security/logs/`
- `../../haetae-ntt-verify/easycrypt-ct/logs/`

The seven current target-extraction summaries are `ntt-extract-summary.txt`,
`fips202-shake-extract-summary.txt`, `keygen-seed-xof-extract-summary.txt`,
`keygen-uniform-xof-extract-summary.txt`,
`keygen-eta-xof-extract-summary.txt`,
`keygen-sampler-callers-extract-summary.txt`, and
`keygen-mode2-parent-extract-summary.txt`; their per-theory EasyCrypt logs are
written under the correspondingly named subdirectories.

The first authored refinement summary is
`keygen-sampler-callers-proof-summary.txt`. Its three compilation logs and its
source-hash, extraction-drift, proof-hole, axiom, and Why3-server logs are under
`keygen-sampler-callers-proof/`.

The target NTT arithmetic refinement writes `ntt-proof-summary.txt`. Its
source-hash, extraction-drift, imported-support hash and identity checks,
fresh EasyCrypt compilation log, proof-hole scan, axiom scan, and Why3-server
log are under `ntt-proof/`. The retained `2026-07-28T06:15:54Z` summary
includes the inverse-NTT bound-18 extension and records `RESULT: PASS`.

The actual mode-2 parent sampler-prefix refinement writes
`keygen-mode2-parent-proof-summary.txt`. Its source-hash check, both extraction
drift checks, shared-theory identity check, 17 fresh EasyCrypt compilation
logs, proof-hole scan, axiom scan, and Why3-server log are under
`keygen-mode2-parent-proof/`.

The gate covering actual mode-2 matrix arithmetic, exact word-level
finalization, totality, root-table rounding, exact rounded FFT initialization,
one-butterfly, inner-prefix, block-prefix, complete-stage, and eight-round
schedule semantics, first-attempt five-slice coefficient reachability,
conditional decoded squared-magnitude/accumulator energy propagation,
ideal-headroom discharge of the exact evolving accumulator safety trace, and
the finite local-tail union-bound schema plus first-attempt measure projection,
and proof-only sampler-to-finalizer composition writes
`keygen-m23-matrix-proof-summary.txt`. Its retained title is “HAETAE mode-2
key-generation matrix, finalization, and singular-word proof verification”.
The `2026-08-04T13:59:34Z` run records the canonical source hash; zero drift for
the 32-file/56-procedure parent, 25-file/31-procedure sampler-caller, and
10-file target-NTT extractions; the project-owned NTT loop support and 18
imported dependency hashes; 53/53 fresh `-no-eco` compilations; and clean
proof-hole, authored-axiom, and
debug-command scans. The individual compilation, hash, drift, scan, and
Why3-server logs are under `keygen-m23-matrix-proof/`.

Logs are evidence, not theorem sources. Each retained summary must identify its
command, source hashes, toolchain record, exit status, and timestamp.
