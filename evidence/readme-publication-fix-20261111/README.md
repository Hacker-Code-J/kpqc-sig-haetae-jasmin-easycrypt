# Fix for public README hash linkage

The full reproduction run in a normal terminal passed 10 steps, from the
environment and socket checks through the NTT target check, before stopping with
`Pinned baseline drift: haetae-easycrypt/README.md`.
The [summary from that run](before-fix-full-summary.json) records the state before
the fix.

During publication preparation, two links to the private thesis folder had been
replaced with evidence inside the repository, but that document change had not
been registered in the publication migration ledger. The
[reviewed change record](reviewed-readme.md) describes those two lines and
identifies the original diff preserved in Git history.

The exact old/current SHA-256 pair for this README was added to the existing
approval mechanism for documentation-only changes. The historical
baseline/toolchain/layout locks, implementations, specifications, proofs, and
existing verification results were unchanged. Checks rejecting unapproved
document changes and implementation/proof changes were retained.

A regression check reading the complete actual checkout reproduced the original
failure before the fix was applied. A further check confirmed that additional
README changes were still rejected. The [verification summary](summary.json)
records the results of the related test suites. Regressions using EasyCrypt were
run after activating the prepared environment.

The 79 hardened outputs were generated and checked again. Compared with the
previous outputs, 78 files, including the implementation, were byte-identical;
the remaining file was generated metadata containing the publication ledger hash.
The 25 fresh compiler extractions also matched the stored models.
([Output comparison](materialization-preservation.json),
[extraction check](extraction-check.log))

This result establishes the documentation hash-linkage fix and its related
checks, not completion of full reproduction. At the time of this record, the next
step was to export the corrected sources afresh and run `full` in a new results
directory. The pre-fix source snapshot and failed results were not overwritten.

Check the records in this directory with `sha256sum --check --quiet SHA256SUMS`.
