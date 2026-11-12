# Full reproduction of the public sources: PASS

The verified sources were a clean export of commit
**`88a543fd07ef268fcbea78d488726cc7652a552f`**. The tool environment previously
installed separately using the public bootstrap was activated, and
`bash scripts/reproduce.sh full --jobs 2` was run once in a normal Linux terminal.
**All 28 steps passed**, and source hashes were unchanged before and after execution.

| Check | Result | Evidence |
| --- | --- | --- |
| Full runner | 28/28 PASS, all exit codes 0 | [Original summary](runner-summary.json) |
| Baseline artifacts, specifications, and proofs | 277/277 PASS | [Proof summary](baseline-summary.json) |
| Hardened targets and baseline proof dependencies | 177/177 PASS | [Proof summary](hardened-summary.json) |
| Executed sources | 1,829 files, clean commit export | [Source manifest](source-manifest.json) |
| Execution environment | Pinned versions and local socket checks PASS | [Environment record](environment.json) |
| Post-run review | Hashes of 28 step logs, hashes and logs for 454 proof targets, and source immutability confirmed | [Verification record](verification.json) |

The 177 hardened targets include 147 baseline dependency files. Thus there were
454 primary-target executions, covering 307 distinct files. Both verifiers used
`-no-eco`, `Proofs:check`, and the existing EOF checks. Re-extraction comparison,
API, sampler, KAT, edge-case, numerical-certificate, CT/SCT, and regression checks
also passed within the full runner.

The run took place on 2026-11-11 from 11:40:56–13:16:50 UTC. Total elapsed time was
**5,753.527 seconds (approximately 1 hour 35 minutes 53 seconds)**, and GNU time
reported a maximum RSS of **3,536,252 KiB (approximately 3.37 GiB)**.
The [resource record](resources.txt) measures this run on this host; it does not
guarantee execution times on other devices.

## Scope of the result

This record closes the gap in full-runner execution with the new tool environment
that remained after the earlier socket restriction and public README hash-linkage
issue. The earlier failures and historical verification records remain preserved;
their execution results have not been rewritten.

The separate installation was on the **same Linux host**. This does not claim
reproduction on another machine or operating system, by an independent researcher,
or in a remote GitHub Actions run. The full-runner PASS covers the stated
components and experiments; it does not establish complete KeyGen/Sign/Verify
correctness, replacement of concrete SHAKE with iid sampling, termination of the
outer Hyperball loop, or complete signature security.

Distinguish the documentation/evidence commit adding this result from the source
commit actually verified, `88a543f`. The bytes and identifiers of the already
verified source archive are retained.

## Complete logs and preservation

One archive preserves the 454 detailed proof logs, both proof summaries, the
28 step logs and runner summary, the original source manifest, execution scripts,
and console and resource records. [Archive metadata](archive.json) gives its
filename, size, and SHA-256. At the time of this record, it was an attachment in
the local publication-preparation directory, with no public download URL, release
tag, or DOI yet assigned. Host paths in the original logs remain as records of
the execution environment at that time.

Check the summaries in this directory with
`sha256sum --check --quiet SHA256SUMS`. The same command in the extracted archive
directory checks the integrity of all logs.
