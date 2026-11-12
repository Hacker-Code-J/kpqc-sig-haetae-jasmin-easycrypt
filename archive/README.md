# Archive of earlier HAETAE work

For the 2026-09-17 restart, only 39 reference files from earlier work were retained
in `legacy/`. The complete earlier implementation, proofs, weekly reports, and
ML-DSA comparison material can be restored from the Git tags below. These materials
record work on earlier sources; they are not verification results for the restarted
HAETAE project.

## Retained materials

Files under `legacy/` retain their original paths. The guides have since been
translated into English; their original versions remain preserved in Git history.
The [English-edition record](../docs/english-edition.md) explains the translation,
PDF rebuilds, exact document migrations, and unchanged historical proof evidence.

| Material | Purpose |
| --- | --- |
| [Latest post-freeze scope](legacy/haetae-topdown-easycrypt/manifests/post-freeze-paper-artifacts.md) | Results, conditions, and remaining obligations for 169 targets |
| [Frozen paper scope](legacy/haetae-topdown-easycrypt/manifests/paper-artifacts.md) · [Paper PDF](legacy/haetae-topdown-easycrypt/latex/main.pdf) | Earlier paper baseline covering 82 targets |
| [Claim ledger](legacy/haetae-topdown-easycrypt/CLAIM_LEDGER.md) · [Theorem dependencies](legacy/haetae-topdown-easycrypt/THEOREM_GRAPH.md) | Distinction between proved claims and unresolved items |
| [Assumptions](legacy/haetae-ref-easycrypt/manifests/assumptions.md) · [Input sources](legacy/haetae-topdown-easycrypt/manifests/source-roots.md) · [Tool versions](legacy/haetae-ref-easycrypt/manifests/toolchain.md) | Prerequisites for reproducing the earlier proofs |
| [Security-model correspondence gaps](legacy/haetae-security/PAPER_CORRESPONDENCE_GAPS.md) | Security-model boundaries to reassess before reuse |
| [NTT proof guide](legacy/haetae-ntt-verify/easycrypt-ct/README.md) | Entry point for NTT code and proofs that may be reused |
| [Theory guide PDF](legacy/haetae-topdown-easycrypt/theory-guide/main.pdf) · [Algebraist guide PDF](legacy/haetae-topdown-easycrypt/algebraist-guide/main.pdf) | Guides with the latest local revisions at the restart; accompanying `.tex`, `.bib`, and README sources |
| [Post-freeze verification summary](legacy/haetae-topdown-easycrypt/logs/verify-post-freeze-summary.txt) | Historical execution record ending in `RESULT PASS post-freeze-theories=169` |
| [In-progress verification summary](legacy/haetae-topdown-easycrypt/logs/verify-all-summary.txt) | Uncommitted log at the restart: 163 compile rows, but no final `RESULT`, so it is not completion evidence |

Source links and relative paths in the guides and ledgers refer to the **complete
earlier tree**. Files not copied here can be found in the tags. The English
translations change document bytes; the original documents, links, and hashes remain
available in Git history. Reproduction requiring the original build scripts and
external proof files must use the complete restored tree as shown below. The earlier
proofs were not rerun as part of the archive reorganization or the translation.

```sh
# Check the integrity of the archived files from the current repository root
sha256sum --check archive/SHA256SUMS
```

## Restoring the complete history

| Archive tag (under `archive/pre-haetae-1.2.0/`) | Preserved state |
| --- | --- |
| `main-20260917` | Earlier `main`, `4bde1207e2a290952d491d5b41c4bd773081e3c4` |
| `ntt-foundation-20260917` | NTT branch, `5a7b487be5fd402e21f3919203af42f21c428e81` |
| `kg-rq-haetae-bridge-20260917` | Last earlier development commit, `ce8b083226596c7c116f1ae95ede95a877117190` |
| `worktree-20260917` | `6177f8db0a2887314dbff213e5ca04234eece58e`, preserving the 20 previously uncommitted files without changes |

The `worktree` snapshot contains the revised guide sources and PDFs, as well as
`.xdv`, `.fdb_latexmk`, and in-progress logs at their original paths. It is the
complete tracked-file tree before the new distribution was introduced and the
archive was reorganized.

```sh
# Open the earlier layout in a separate directory, even without the tags
git worktree add --detach ../haetae-previous \
  6177f8db0a2887314dbff213e5ca04234eece58e

# Inspect a file before copying it
git show 6177f8db0a2887314dbff213e5ca04234eece58e:haetae-ref-jasmin/jasmin/sampler.jinc
```

The original projects are connected by relative paths and pinned manifests, so do
not move a single proof root into this directory and run it in isolation. Check the
required tool versions and verification scripts in the `worktree`, then selectively
bring the needed material into new work.

Previously untracked local files and build outputs were moved to
`.omx/restart-backup/haetae-1.2.0-20260917/legacy-tree/` on this computer for separate
preservation. That local backup is not in Git. The Git snapshots above are the
basis for durable recovery.

## Scope of the main-branch reorganization

The earlier `main` → NTT → bridge commits form one ancestry chain, so `main` was
advanced while retaining history. The two old local working branches were removed
after their states were preserved as tags. The historical snapshot commits are part
of the published `main` history, so other clones can restore them by the commit
hashes above. At the time of the reorganization, the four archive tags were retained
locally and had not been published remotely because the GitHub app tools used then
did not support publishing tags. Remote branch deletion and GitHub settings changes
were outside the scope of that work.

Duplicate reference implementations, profiling and comparison material, and
intermediate outputs were removed from the current tree. History was retained;
there was no history rewrite to reduce the size of `.git`.
