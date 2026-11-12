# Fastexp provenance and licensing evidence for identical bytes

The scope is the single file
[`haetae-easycrypt/theories/ntt/Fastexp.ec`](../../haetae-easycrypt/theories/ntt/Fastexp.ec).
On 2026-11-12, the official successor Formosa repository was checked for a
**byte-identical file** and an explicit `CC0-1.0 OR Apache-2.0` distribution
notice. The notice and both license texts from that successor revision are
preserved. Existing verified sources, TSVs, lockfiles, and the root MIT license
are unchanged.

## Identity and scope

- Local file SHA-256: `a1f7a3562c743eab602cf98f6380339c63aa3824448380e570b1dcbbb3e450b3`
- Git blob: `f7c412959f8d359619e592b8152e9537fc227495`
- Revision distributing the identical file under an explicit license:
  [`formosa-crypto/formosa-libjade@589038bbae572525ff6a8281f6bc07fa5a31ff7b`](https://github.com/formosa-crypto/formosa-libjade/blob/589038bbae572525ff6a8281f6bc07fa5a31ff7b/proofs/mlkem/eclib/Fastexp.ec)
- That revision's [LICENSE](https://github.com/formosa-crypto/formosa-libjade/blob/589038bbae572525ff6a8281f6bc07fa5a31ff7b/LICENSE)
  and [README License section](https://github.com/formosa-crypto/formosa-libjade/blob/589038bbae572525ff6a8281f6bc07fa5a31ff7b/README.md#license)
  explicitly offer a choice of CC0 1.0 or Apache 2.0. The README identifies
  `bench/third_party/` submodules as having separate terms; this file resides
  under `proofs/mlkem/eclib/`.

The publication basis recorded for this file is **identical bytes in a later
explicitly licensed revision**. This does not assert that the earlier
`475b874...` revision had a license at that time or that the later notice
applies retroactively. The local root MIT notice is not used as an independent
basis for relicensing this external support file. These findings do not extend
to other NTT support files or all historical Formosa files.

## Verified history

| Event | Immutable commit | Verified fact |
| --- | --- | --- |
| File added | [`b94dc0d4f553e82a656d2382f56d2edbc9ce3282`](https://github.com/formosa-crypto/formosa-libjade/commit/b94dc0d4f553e82a656d2382f56d2edbc9ce3282) | 2022-04-21, commit author Manuel Barbosa. Added `proof/correctness/eclib/Fastexp.ec`. |
| Path moved | [`3ad502b30e3f8205043564760b1be51e8efda8c1`](https://github.com/formosa-crypto/formosa-libjade/commit/3ad502b30e3f8205043564760b1be51e8efda8c1) | 2022-04-28, commit author Manuel Barbosa. Moved to `proof/eclib/Fastexp.ec` without changing its bytes. |
| Comments added | [`875080867bc7c457f19a7602eb047ad1c9a8f093`](https://github.com/formosa-crypto/formosa-libjade/commit/875080867bc7c457f19a7602eb047ad1c9a8f093) | 2022-07-05, commit author Antoine Séré. Added 6 comment/blank lines, producing the current blob. |
| Existing audit baseline | [`475b87434506280fdfa1a1ba5da0af3787e00579`](https://github.com/formosa-crypto/formosa-libjade/commit/475b87434506280fdfa1a1ba5da0af3787e00579) | Identical file in the existing Formosa checkout. No applicable license for this file was established from that tree. |
| Successor placement | [`94a8711044b668b67cb503f8b5af9826db3aa470`](https://github.com/formosa-crypto/formosa-libjade/commit/94a8711044b668b67cb503f8b5af9826db3aa470) | 2026-06-29, the successor tree contains the same blob at `proofs/mlkem/eclib/Fastexp.ec`. |
| Explicit license added | [`b301e356c3fc52fa6522be5445534d228e809548`](https://github.com/formosa-crypto/formosa-libjade/commit/b301e356c3fc52fa6522be5445534d228e809548) | 2026-11-09, commit author Pierre-Yves Strub. Added the SPDX expression and both texts, with the same terms stated in README and opam metadata. |
| Distribution checked here | [`589038bbae572525ff6a8281f6bc07fa5a31ff7b`](https://github.com/formosa-crypto/formosa-libjade/tree/589038bbae572525ff6a8281f6bc07fa5a31ff7b) | Contains exactly the same blob as the current local file together with the licensing notices above. |

The GitHub [commit comparison](https://github.com/formosa-crypto/formosa-libjade/compare/475b87434506280fdfa1a1ba5da0af3787e00579...589038bbae572525ff6a8281f6bc07fa5a31ff7b)
also confirms that the existing pin is an ancestor of the successor revision.
Commit authors are recorded as history fields; those fields alone do not
identify the original author or all rights holders. This investigation did not
establish an earlier original source predating the file's addition in 2022.

The local [NTT provenance TSV](../../haetae-easycrypt/manifests/ntt-support-origin.tsv)
continues to preserve the earlier research snapshot's paths and hashes. Local
Git history records the earlier path at `bc20daa...` and the current path at
`c5313fa...`. This record supplements the TSV with the verified external
history and later licensing evidence for the same bytes; it neither replaces
nor modifies the TSV.

## Preserved notices

The following are verbatim files retrieved from the successor revision above,
verified by Git blob and SHA-256. Their identities are listed in the
[machine-readable record](fastexp.json).

- [Upstream SPDX notice](../../LICENSES/formosa-libjade/UPSTREAM-LICENSE.txt)
- [CC0 1.0 text](../../LICENSES/formosa-libjade/CC0-1.0.txt)
- [Apache 2.0 text](../../LICENSES/formosa-libjade/Apache-2.0.txt)
- [Upstream contributors](../../LICENSES/formosa-libjade/CONTRIBUTORS.md)

The contributors file covers the project as a whole; it does not assert that
every contributor authored this file. The root license and this file's external
notices retain their respective scopes.

## Repository move

The [move notice](https://github.com/formosa-crypto/formosa-mlkem/blob/d1e64d5fee2157b47e5030c4f0bdc07bb36a7bde/README.md)
at the former `formosa-crypto/formosa-mlkem` location points to the official
successor repository. Historical commits are available in the successor.
This location change does not change existing file pins or verification results.
