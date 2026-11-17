# Research artifact publication

An artifact release identifies a Git commit and verification summaries. Cite
the release tag or commit hash and link the summary for the result used. Each
summary applies to the source hashes it records.

[Version 1.0.1](https://github.com/Hacker-Code-J/kpqc-sig-haetae-jasmin-easycrypt/releases/tag/haetae-sampler-ntt-proofs-v1.0.1)
was published on 2026-11-12. The current development sources contain the
later EasyCrypt 2026.10 migration described below.

## Selected initial publication scope

The initial release contains implementation/specification/proof sources,
reproduction scripts and tool-installation instructions, license notices,
verification results and logs. Compiler/prover executables, installed tool
stacks and VM/container images are not distributed. Install the compiler and
prover versions listed in the [environment guide](../env/README.md) before
running the reproduction commands.

## Recorded reproduction

The current development sources incorporate the
[EasyCrypt 2026.10 proof port](../evidence/easycrypt-2026.10-20261116/README.md).
The recorded run checked 14 Gaussian probability/termination proof files,
10 verifier regression tests and four tests that reject incomplete or false
proofs. In `GaussianRetryCore.ec`, the edits add a distribution-mass
nonnegativity step to `gr_retry_phoare` and a `0 <= 1` step to
`gr_retry_lossless`. Theorem statements, assumptions and numerical bounds are
unchanged. `env/opam-switch.export` pins EasyCrypt 2026.10. The `full`
reproduction command has not been run under that pin; the record below describes
the earlier 2026.09 execution.

On 2026-11-11, a clean source export of commit **`88a543f`** passed **all 28 full-runner
stages** using the 2026.09 tools separately installed by that revision's public
bootstrap. The run
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

Earlier environment and document-integrity failures are recorded in the
[socket restriction report](../evidence/release-candidate-20261111/README.md) and
[document-hash report](../evidence/readme-publication-fix-20261111/README.md).

## Before freezing sources

1. Check each claim in the [research map](research-map.md) against the actual
   theorem, premises and command. Distinguish complete-API obligations, iid
   models, and the original/hardened implementations.
2. Run `bash scripts/reproduce.sh full` on the release-candidate sources; retain
   the runner's input hashes, commands, logs and per-stage results.
3. Include sources, required evidence and license notices in the publication
   file list. Exclude local configuration and generated build files.
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
- Deposit the release in an institutional repository or research artifact
  archive. Record its assigned DOI or archive record URL in
  [CITATION.cff](../CITATION.cff) and the paper.
- The current `CITATION.cff` identifies the software repository. Add publication
  metadata when it is available.

## Revisions

Use a new tag and verification record for subsequent fixes or new proofs.
Explain their effect on paper claims or measurements and the applicability of
prior releases. Distinguish naming/documentation changes from implementation
or theorem changes.
