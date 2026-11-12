# Research artifact publication

An artifact cited by a paper must identify both a specific source state and
the verification records produced from it. Distinguish the current development
branch from the results used at submission. This guide describes the publication
procedure; it does not by itself establish a release or DOI.

## Selected initial publication scope

The initial release contains implementation/specification/proof sources,
reproduction scripts and tool-installation instructions, license notices,
verification results and logs. Compiler/prover executables, installed tool
stacks and VM/container images are not distributed. System source-package
acquisition for a possible tool-binary distribution is not a prerequisite for
this source release. Actual reproduction requires the tools described in the
[environment guide](../env/README.md).

## Recorded reproduction

On 2026-11-11, a clean source export of commit **`88a543f`** passed **all 28 full-runner
stages** using tools separately installed by the public bootstrap. The run
executed 277 original targets and 177 hardened/dependency targets, and source
stability and log hashes were checked. The
[full reproduction record](../evidence/full-replay-20261111/README.md) identifies
sources, tools, resources and scope. This was a separate installation on the
same Linux host, not an independent-machine replay or a publication event.

The subsequent [Fastexp provenance review](provenance/fastexp.md) identified an
official, explicitly licensed revision containing identical bytes and preserved
the license texts. Distribute the new `LICENSES/formosa-libjade/` notices and
provenance materials alongside the tested `88a543f` source archive. Retain the
verified files, locks and original archive; adding notices is not a new proof run.

The earlier [socket restriction record](../evidence/release-candidate-20261111/README.md)
and [document-hash transition repair](../evidence/readme-publication-fix-20261111/README.md)
remain development history. Historical locks, proofs and earlier outcomes are
not overwritten with a later PASS.

## Before freezing sources

1. Check each claim in the [research map](research-map.md) against the actual
   theorem, premises and command. Distinguish complete-API obligations, iid
   models, and the original/hardened implementations.
2. Verify changed sources and extractions. Do not copy an earlier PASS or merely
   replace hashes to approve a new result.
3. Review the publication file list and Git history. Include required evidence;
   exclude personal configuration, credentials, private manuscripts and unrelated
   large outputs. Treat history rewriting as a separate operation.
4. Check the [provenance guide](THIRD-PARTY.md) and the inclusion of original
   licenses and notices.

## Separate reproduction

Clone the release-candidate commit into a new directory and configure its tools
according to the [environment guide](../env/README.md). Run without existing
build directories, personal home-path dependencies or a sibling thesis directory:

```sh
bash scripts/reproduce.sh quick
bash scripts/reproduce.sh full
```

For an uncommitted working tree, a source export can provide a separate check.
It is not a Git release: `SOURCE-MANIFEST.json` records the base commit,
working-tree status and file hashes. Choose an output path that does not exist:

```sh
python3 scripts/export-source.py /tmp/haetae-artifact
cd /tmp/haetae-artifact
bash scripts/reproduce.sh quick
bash scripts/reproduce.sh full
```

Preserve the source commit or file-hash inventory, actual commands, tool/prover
versions, target list, exit codes, elapsed time and resources. Failures, timeouts
and omitted checks are not PASS. If checked sources change after recording,
rerun affected checks. Earlier records remain evidence of their original sources.

## Citable releases

- Attach a new release tag to the commit that completed the documented
  reproduction. Never move an already cited tag to another commit. The tag need
  not repeat the reference implementation's distribution version.
- Provide source archives, reproduction instructions, verification summaries and
  checksums. A source archive lets readers avoid downloading the entire large
  historical Git repository. CI status alone does not establish that all checks
  used in the paper ran.
- Preserve the final release in an institutional repository or long-term research
  artifact archive as well. Once a persistent identifier actually exists, record
  it in [CITATION.cff](../CITATION.cff) and the paper.
- Do not invent a thesis title, degree information or publication identifier
  before they are finalized. The current CITATION describes the software repository.

## Revisions

Use a new tag and verification record for subsequent fixes or new proofs.
Explain their effect on paper claims or measurements and the applicability of
prior releases. Distinguish naming/documentation changes from implementation
or theorem changes.
