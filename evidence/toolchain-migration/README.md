# Historical toolchain-migration verification evidence

This directory preserves selected evidence from the HAETAE toolchain-migration
verification performed on 2026-10-10. The underlying execution records retain their
original bytes; this explanatory README has been translated into English.
**These are not full verification results for the current working tree.**
Within the records, `current` refers to the sources at the time of verification.
Historical PASS results do not automatically apply to subsequently added NTT
theorems, directory renaming, or publication-preparation changes.

| Evidence | Recorded scope |
| --- | --- |
| [Final result](haetae-full-proof-result.json) | 260 baseline and 30 hardened targets: 290 primary targets PASS |
| [Per-target results](proofs/summary.json) | Execution commands, source hashes, exit codes, times, and final logs |
| [Relocation index](index.json) | Historical-path digests, public-copy paths, sizes, and SHA-256 |
| [Final hardened gates](haetae-provenance-finalization/summary.json) | Materialization, extraction, and verifier regression records from that time |

The 260 baseline targets consist of 207 specifications/proofs and 53 generated
artifacts. Including the 30 hardened targets, the total of 290 is the **number of
files executed as primary verification targets**, not a theorem count. Hashes of
the original result and per-target results match the `full_replay` entry in the
existing [migration manifest](../../haetae-easycrypt/manifests/2026.09-migration.json).

All logs for the 290 final targets and copies of the primary sources actually
checked are included. The HAETAE input-hash list, small final-gate records, and
diagnostic files explicitly referenced by the migration manifest are also included.
Unrelated projects, thesis manuscripts and presentation materials, and every failed
candidate or intermediate experiment were not copied wholesale. Thus this does not
mean that every file referenced by fields such as `prior_attempts` in the original
JSON is included.

The original results retain their `/home/...` and `/tmp/...` paths and directory
names from that time as part of the historical record. The schema-2 `index.json`
uses `historical_path_sha256` and `historical_alias_sha256` instead of copying raw
host paths into its metadata. The checker matches SHA-256 digests of the UTF-8
encoded paths recorded in the untouched original result JSON to the corresponding
entry's English relative `path`. There is no need to execute or visit external
paths. The original index remains recoverable from Git commit `a4c259a`; source
and log bytes are unchanged. This index checks integrity across file relocation;
it does not rerun proof checks.

From the repository root, use the following command to check copy hashes, pinned
result hashes, target counts, and the actual primary-source copy for each target:

```sh
python3 scripts/check-evidence.py
```

For reproduction of the current sources, follow the [environment guide](../../env/README.md)
and [repository guide](../../README.md). This evidence alone does not claim to
reconstruct the complete historical execution environment and all source dependencies.
