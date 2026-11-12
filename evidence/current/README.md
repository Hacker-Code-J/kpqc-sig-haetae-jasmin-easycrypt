# Publication-preparation verification results

[summary.json](summary.json) records the original summaries, logs, and file hashes
for each run. [source-snapshot.json](source-snapshot.json) identifies the source
at verification time. This is a snapshot of an uncommitted working tree, not a
GitHub release or DOI.

| Check | Result | Evidence |
| --- | --- | --- |
| Baseline implementation artifacts, specifications, and proofs | 277/277 PASS | [Summary](baseline-proofs/summary.json) |
| Hardened specifications and proofs, including baseline proof dependencies | 177/177 PASS | [Summary](hardened-proofs/summary.json) |
| Quick reproduction from sources without caches | 20 steps PASS | [Summary](clean-source-quick/summary.json) |
| Quick reproduction with tools freshly installed from public sources | 20 steps PASS | [Summary](bootstrapped-quick/summary.json) |
| Reference KAT, numerical certificates, edge cases, CT/SCT, and re-extraction comparison with the new tools | 8 steps PASS | [Summary](supporting-checks/summary.json) |

The 177 hardened targets include 147 baseline specification and proof dependencies.
The two full proof checks executed 454 primary targets, covering 307 distinct files.
Both verifiers used `-no-eco`, `Proofs:check`, and an EOF completion check. The
recorded hash of each target was compared again with the sources at that time.

The full proof commands were run separately in the existing supported tool
environment. The quick execution checks and supporting checks used a source export
excluding build caches, Git history, and the private thesis folder. The independent
installation used a separate opam root/switch on the same Linux host. This does not
mean execution in a new virtual machine or on another operating system.

At the time of this record, the complete proof set had not been rerun in the newly
built tool environment, and GitHub Actions had not been run remotely. This record
also does not claim that every step of the full reproduction command was executed
in a single runner invocation. Consult the individual logs for per-step commands
and tool hashes. The quick checks run verifier regressions and selected actual proof
checks, but do not replace the full proof checks.

[bootstrap/](bootstrap/) preserves the initial environment-installation logs and
the recheck logs for the final reviewed scripts. The environment executables were
newly built, so their hashes may differ from executable hashes in historical
records. Fresh Jasmin extractions matched the stored programs byte for byte.
[resources.txt](bootstrapped-quick/resources.txt) records the resources used by the
quick checks in the new environment. The quick and supporting checks also verified
that source snapshots were unchanged before and after execution. Host paths in the
original JSON and logs are records of the execution environment at that time.

These results cover research components and the stated experiments. They do not
establish complete signature-API correctness, replacement of concrete SHAKE with
iid sampling, termination of the outer Hyperball retries, or complete signature
security.

Check the integrity of the stored evidence from the repository root:

```sh
(cd evidence/current && sha256sum --check SHA256SUMS)
```
