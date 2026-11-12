# Release-candidate checks and full reproduction attempt

Status at the time of this record: **release candidate prepared; full reproduction
in the new environment incomplete**. This directory records new runs from
2026-11-11, including failures. It does not change the results in
[`evidence/current`](../current/README.md) or the toolchain-migration evidence.

## Public source inventory

[`executed-source-manifest.json`](executed-source-manifest.json) identifies the
1,792 files (23,431,779 bytes) exported without build caches, Git history, or the
private thesis folder. The base commit was
`f836bf6f0e8e2107f1e5f839facf63a3e66fa356`; the actual execution target was the
uncommitted working tree on top of it. The base commit alone does not reconstruct
that execution target.

[`source-inventory.json`](source-inventory.json) maps 613 tracked files from the
four earlier implementation/proof directories to their new paths. Of these,
383 are byte-identical, 147 are changed, and 83 are generated `Array*`/`WArray*`
helpers removed during the toolchain migration. No missing ordinary
implementation, specification, or proof files were found. This does not establish
completion of an independent review of all changed research content. Separately,
fresh re-extraction equivalence checks with the new tools passed for 58 baseline
and 25 hardened artifacts.

## Actual execution results

The new tools used the separate opam root/switch previously configured through
the public bootstrap. The full execution command was:

```sh
bash scripts/reproduce.sh full --jobs 2 --output /path/to/new-results
```

| Check | New run result | Evidence |
| --- | --- | --- |
| Full runner | **FAIL**, 8 of 28 steps PASS, step 9 failed | [Original summary](full-replay/summary.json) |
| Environment, evidence, public-tool regressions, baseline hashes, Jasmin API/sampler/KAT | PASS | Steps 1–8 and logs in the summary above |
| EasyCrypt regressions | Why3 server connection failed | [Step 9 log](full-replay/09-easycrypt-gates.log) |
| Baseline re-extraction comparison | 58 artifacts PASS | [Log](fresh-extraction-check.log) |
| Hardened materialization and re-extraction comparison | 79 materialized files, 25 artifacts PASS | [Log](fresh-hardened-extraction-check.log) |
| Public-tool regressions after adding preflight diagnostics | 22 PASS | [Log](public-tool-regressions.log) |
| Environment check after adding preflight diagnostics | Expected FAIL, explicitly reporting local socket permission denial | [Result](early-environment-check.json) |

The full runner returned exit code 1 after 49.65 seconds, with unchanged source
hashes before and after execution. Maximum RSS was 298,828 KiB. These values
measure resource use only up to the failure point, not the cost of a complete
proof run. See the [resource record](full-resources.txt).

Both AF_UNIX and AF_INET diagnostics in the same isolation context as the run
returned `EPERM`. The Why3 server logging diagnostic also recorded
`error binding socket`.
([Socket diagnostic](replay-context-bind-probe.json),
[server diagnostic](why3-server-logged.json))
This is not classified as an ordinary tool-version mismatch or a mathematical
proof failure. The supported external-server entry point was also unavailable
because it could not create a socket in this execution context.

## Next execution and record boundaries

At the time of this record, the required next step was to run `full` with the same
public sources and pinned environment in a new results directory on Linux with
local Unix sockets permitted. Skipping checks, relaxing timeouts, or copying an
existing PASS would not replace this failure. This run did not reach the full
baseline or hardened proof stages and does not claim a new full proof PASS.

After the run, socket preflight diagnostics in `env/check.py`, their regression
tests, public documentation links, and this record were added. The executed-source
manifest still identifies the sources before those additions. Proofs,
specifications, Jasmin sources, and verification criteria were unchanged by that
work. The final release-candidate file inventory is identified by the
`SOURCE-MANIFEST.json` generated when the release candidate is exported again.

Verify the preserved files in this folder as follows:

```sh
(cd evidence/release-candidate-20261111 && sha256sum --check SHA256SUMS)
```
