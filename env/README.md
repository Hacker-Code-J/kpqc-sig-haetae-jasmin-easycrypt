# Reproduction environment

The supported platform is Linux x86-64. The following compiler and prover
combination is fixed for this artifact. If tools are already installed, start
with `bash scripts/check-environment.sh`. It also checks permission to create
and listen on a local Unix socket, as required by the Why3 server. If the
execution environment prohibits this, it reports `local_unix_socket: FAIL`
with the cause and stops.

| Tool | Baseline |
| --- | --- |
| Jasmin compiler / extractor | 2026.09.0, official extracted-source release |
| EasyCrypt | r2026.09, commit `2aaa14acf7b2ce234b475f24f9e85ba0bdaeb024` |
| Why3 | 1.8.2 |
| Main OCaml switch | 5.4.0; package versions and metadata recorded in `opam-switch.export` |
| Alt-Ergo | 2.6.0 |
| Z3 | 4.12.6 |
| CVC4 | 1.8 |
| CVC5 | 1.2.1, official Linux x86-64 static distribution |

## Installation

The documented installation and hosted CI use Ubuntu 22.04 (Jammy). Install
the required system packages there. Only the system package
commands below require administrator privileges.

```sh
sudo apt-get update
sudo apt-get install -y opam build-essential cmake ninja-build git python3 python3-distutils \
  wget unzip bzip2 pkg-config libssl-dev libgmp-dev libpcre2-dev libppl-dev \
  libmpfr-dev zlib1g-dev autoconf automake libtool cvc4
bash env/bootstrap.sh
source env/activate.sh
bash scripts/check-environment.sh
```

The fixed [Z3 4.12.6 opam recipe](https://github.com/ocaml/opam-repository/blob/master/packages/z3/z3.4.12.6/opam)
declares `python3-distutils` on Debian-family systems. Ubuntu provides this
package in [Jammy](https://packages.ubuntu.com/jammy/python3-distutils), but not
Noble (24.04). The bootstrap checks that existing dependency before importing
the compiler switch and reports an actionable error if it is missing. The CI
runner matches the Ubuntu 22.04 base of the successful local reproduction.
This platform correction does not change compiler/prover versions or package
source recipes; Ubuntu 24.04 is not the supported installation recipe here.

`bootstrap.sh` configures the environment only under `env/.opam-root/`,
`env/_opam/`, `env/provers/`, `env/config/` and `env/downloads/`. It does not
modify shell startup files or an existing global opam switch. Run
`source env/activate.sh` in each new shell. Because Alt-Ergo requires
`cmdliner < 2`, the provers use a separate OCaml 5.2.1 switch. Alt-Ergo and Z3
versions are fixed, while opam resolves that prover switch's transitive
package dependencies during installation. The main compiler switch uses the
metadata in the complete switch export.

The export replaces private `file://` source references from the original
installation with the following public sources. Executable hashes can differ
between build environments and are recorded separately for each new execution.
Successful installation alone does not establish proof reproduction.

- [Official Jasmin release](https://github.com/jasmin-lang/jasmin/releases/tag/v2026.09.0),
  `jasmin-compiler-v2026.09.0.tar.bz2`:
  SHA-256 `11fec571efb9f7b3a47fea324b4e2a68289e0b73b2248d237eccf139b5218190`.
- [Pinned EasyCrypt source](https://github.com/EasyCrypt/easycrypt/tree/2aaa14acf7b2ce234b475f24f9e85ba0bdaeb024).
- [Official CVC5 release](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.2.1),
  `cvc5-Linux-x86_64-static.zip`:
  SHA-256 `6d44abc233980a14d72cc5809287d27c3335b1d6ee863381d0b5ffcbd0d8de56`.

## Quick checks and full reproduction

Run from the repository root:

```sh
bash scripts/reproduce.sh quick
bash scripts/reproduce.sh full
```

`quick` checks the environment, published historical-evidence integrity,
upstream hashes, Jasmin API/sampler/KAT execution, EasyCrypt verifier regressions,
NTT target inventories, hardened-source materialization and extraction-provenance
regressions, and the hardened implementation's API/KAT behavior. It does not
rerun the complete proof collection.

`full` additionally checks the C-reference KAT, regeneration of numerical
certificates, constructed Hyperball boundary cases, CT/SCT, and all selected
original/hardened proofs. The full proof commands compare fresh Jasmin
extractions and execute each selected local proof as a main target. A changed
extraction is not automatically overwritten to make a check pass.

```sh
bash scripts/reproduce.sh full --jobs 2 --output /tmp/haetae-reproduction
```

The output directory must be new and located outside the source tree or under
its root `build/` directory. The default is
`build/reproduction/<UTC timestamp>-<mode>/`. Other output paths within the
source tree are rejected before writing. `summary.json` records stage commands,
status, exit codes, elapsed time and log hashes. Before execution, the runner
records actual source-file SHA-256 values and Git state. If an exported
`SOURCE-MANIFEST.json` is present, it first checks the actual file contents and
inventory against that manifest. Source changes detected at the end cause failure.

The runner stops at the first failing stage and returns a nonzero status.
Detailed project proof logs are written under their respective `logs/` directories.
Existing `manifests/verification-results.json` and preserved historical evidence
are not updated. CI stores new execution logs in a separate artifact.

## Separate reproduction and resources

Clone the exact commit used in the paper into a new directory, then install
the tools and run full reproduction as above. Do not copy existing `build/`,
`logs/`, `.eco` caches or a private thesis directory. System-package and source
downloads require network access; the checks themselves do not download
additional materials after installation.

All 28 stages of the full runner passed on source commit `88a543f` using the
environment separately installed by the public bootstrap. That execution took
about **1 hour 35 minutes 53 seconds**, with GNU time maximum RSS
**3,536,252 KiB (about 3.37 GiB)**. The
[execution record](../evidence/full-replay-20261111/README.md) identifies tools,
sources, logs and resources. This was on the same Linux host; it does not
promise installation/runtime costs or memory use on another machine.
`--jobs 2` is the default build concurrency; EasyCrypt targets execute sequentially.

Use measured times from the resulting `summary.json` for publication. Keep the
verifiers' default prover timeouts. Record any non-default `EC_TIMEOUT`,
`EC_MAX_PROVERS` or `WHY3_SERVER_SOCKET` values. If an isolated environment
cannot start the Why3 server, use a normal Linux shell or an execution
environment that permits local sockets.

The installation follows [opam switch import](https://opam.ocaml.org/doc/man/opam-switch.html)
and the [installation guide for the selected EasyCrypt release](https://github.com/EasyCrypt/easycrypt/blob/r2026.09/INSTALL.md).
