# English edition and historical evidence

The maintained documentation, archived research guides, and their PDFs are
published in English. Translation does not change the scope of the recorded
mathematical results. In particular, the earlier guides retain their frozen and
post-freeze boundaries, conditional correctness statements, and open obligations.
Building a translated PDF is not a proof replay.

## Original documents and exact changes

The original documents are recoverable from Git history at
`a4c259a52debb6ae6509f5bcf92a1594178854fd` (the maintained documentation was already
English at that commit). The preceding publication revision is
`3336e4290e56b7588f0b8abe1ae30366730f461b`.
[The translation record](english-edition.json) identifies changed documents,
PDFs, and metadata by their before/after SHA-256 values. The archive checksum
list now authenticates the English edition; original checksum lists remain in
Git history. Evidence checksum lists change only for translated explanatory
documents and the replacement of the displayed README patch by its English
explanation. Execution logs, source snapshots, proof results, and their hashes
remain unchanged.

The hardened materializer retains the original baseline, toolchain, and layout
locks. Its exact publication ledger additionally permits the reviewed English
guide bytes and archive checksum list. It does not permit arbitrary changes to
proofs, implementation files, or execution results.

## Historical paths are data

Original execution records contain the host paths used at the time, including
non-English directory names. These records remain byte-identical: changing a
recorded path would invalidate the evidence hashes. This is an English edition
of the repository's authored content, not a rewrite of historical executions or
Git history.

The portable toolchain-migration index uses English repository-relative paths
and SHA-256 identities for the exact UTF-8 historical paths. The checker hashes
paths from the unchanged original results and resolves them through this index.
It still checks file contents, anchors, target counts, and the checked source
for every target. No access to the original host directories is required.
The original index can be recovered using its recorded Git commit and SHA-256.

The earlier Korean README diff has an
[English explanation](../evidence/readme-publication-fix-20261111/reviewed-readme.md)
with the original Git location and hash. It is not represented as a new patch
or a newly performed verification.

## Publication boundary

Previously published tags, source archives, and verification archives are not
replaced by this translation. A new source package must identify its own commit
and distinguish it from the source commits checked by the historical proof runs.
Any new release title and tag require the repository owner's approval.
