# Toolchain Record

Recorded on 2026-07-13 in the initial Phase 0 workspace.

## Repository and host

| Item | Recorded value |
| --- | --- |
| Repository base commit | `a20d5efa83e4fbedbd6142c28aa942e2cd5598be` |
| Kernel | `Linux 5.15.0-179-generic x86_64 GNU/Linux` |
| C compiler | `cc (Ubuntu 11.4.0-1ubuntu1~22.04.3) 11.4.0` |
| GNU Make | `4.3` |
| SHA-256 utility | GNU coreutils `8.32` |

The base commit fingerprints tracked baseline proof sources. The new
`haetae-ref-easycrypt` workspace was uncommitted when this record was created.

## Verification tools

| Tool | Version/configuration | Resolved binary | SHA-256 |
| --- | --- | --- | --- |
| EasyCrypt | `easycrypt config` reports `git-hash: n/a`; installation is under the `easycrypt-5.2` opam switch | `/home/hacker-code-j/.opam/easycrypt-5.2/bin/easycrypt` | `1a943567bc94f43bbf427b52376b5deb5e0d79fd9049529302822c72d7ea4c3e` |
| Jasmin compiler | `Jasmin Compiler 2026.03.0` | `/usr/local/bin/jasminc` | `cf8dde7cdd8fe7151d33a5948bac8e0ee57419ca1d57b4dfc21dab2569fa0c45` |
| jasmin2ec | `Jasmin Compiler 2026.03.0` | `/usr/local/bin/jasmin2ec` | `3a9fde9a1237d791fa4b38b4a908f4d98f637a5fba81f74f8e2417c0190f6196` |
| Why3 | `Why3 platform 1.8.0` | `/home/hacker-code-j/.opam/easycrypt-5.2/bin/why3` | `4511d74d5e937b447c58b94412277fa123a88a097e46e586cf2b3bac728d25fc` |
| Z3 | `Z3 4.12.6, 64-bit` | `/home/hacker-code-j/.opam/easycrypt-5.2/bin/z3` | `574aa7f011ef3c34c4ea1fd7255251d5054107124da0bcbbb3de82d12bfaa2d5` |
| C compiler binary | GCC 11.4.0 | `/usr/bin/cc` | `821af3c74506283c179ca413bb33e6b528805a4dd8a5c09df125e5ad560a9e89` |

EasyCrypt's active configuration reports these known provers:

- Alt-Ergo 2.6.0
- CVC4 1.8.0
- CVC5 1.2.1
- Z3 4.12.6

The active EasyCrypt load path includes Jasmin's EasyCrypt library at
`/home/hacker-code-j/jasmin/eclib` and the EasyCrypt theories installed under
the `easycrypt-5.2` opam switch.

## Re-recording policy

Tool versions alone are insufficient when version metadata is absent or
ambiguous. A reproduction report must include both the semantic version (when
available) and the binary hash. Any tool or configuration change requires a
new verification run and an update to this record.
