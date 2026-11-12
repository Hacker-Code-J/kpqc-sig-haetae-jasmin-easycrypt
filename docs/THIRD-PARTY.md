# Sources of code and proof materials

This inventory locates the notices and provenance records included in the
repository. It does not replace the licenses, copyright statements, or
individual notices in the original files.

| Material | Source and notices | Repository evidence |
| --- | --- | --- |
| Project documentation and EasyCrypt research code authored here | MIT notice by Ji, Yonghyeon | [Root LICENSE](../LICENSE), [EasyCrypt LICENSE](../haetae-easycrypt/LICENSE) |
| HAETAE reference implementation and official KAT | Team HAETAE distribution; existing MIT notice preserved | [Original LICENSE](../HAETAE/LICENSE), [distribution provenance](HAETAE.md), [per-file SHA-256](UPSTREAM-SHA256SUMS) |
| Reference-derived code in the Jasmin implementation and hardened variant | Existing notices for Team HAETAE-based code preserved | [Jasmin LICENSE](../haetae-jasmin/LICENSE), [hardened-variant LICENSE](../haetae-hardened/LICENSE) |
| KAT generation code | NIST-developed software notice in the file headers | [PQCgenKAT_sign.c](../haetae-jasmin/kat/PQCgenKAT_sign.c), [kat_api.h](../haetae-jasmin/kat/kat_api.h) |
| Reference SHAKE/Keccak code | Original notice identifying Ronny Van Keer's SUPERCOP implementation and TweetFips202 by Gilles Van Assche, Daniel J. Bernstein, and Peter Schwabe as its basis | [fips202.c](../HAETAE/reference_implementation/src/fips202.c) |
| Earlier NTT/SHAKE support theories | Files, commits, ported hashes, and changes from earlier research snapshots | [NTT provenance](../haetae-easycrypt/manifests/ntt-support-origin.tsv), [SHAKE provenance](../haetae-easycrypt/manifests/shake-support-origin.tsv) |
| `theories/ntt/Fastexp.ec` support theory | `CC0-1.0 OR Apache-2.0` notice in the official successor Formosa revision distributing identical bytes; existing pin retained | [File-specific provenance and licensing evidence](provenance/fastexp.md), [preserved upstream notice](../LICENSES/formosa-libjade/UPSTREAM-LICENSE.txt) |
| References for mathematical specifications and distribution definitions | Correspondence to formulas defined in the HAETAE specification, papers, and thesis | [Specification source inventory](../haetae-easycrypt/manifests/specification-sources.json) |

Jasmin, EasyCrypt, Why3, SMT provers, and OpenSSL are external tools used for
reproduction. The [environment guide](../env/README.md) describes installation
and required versions. Consult each tool distribution for its license; the
repository license does not apply to the entire toolchain.

Recording a reference PDF's link, hash, and use does not mean that the PDF
itself is redistributed in this repository. Paths and version labels in
historical files are preserved to identify the original materials.

## Additional provenance of earlier support theories

`haetae-easycrypt/theories/ntt/Fastexp.ec` is byte-identical to
[`proof/eclib/Fastexp.ec`](https://github.com/formosa-crypto/formosa-libjade/blob/475b87434506280fdfa1a1ba5da0af3787e00579/proof/eclib/Fastexp.ec)
at pinned Formosa ML-KEM commit `475b87434506280fdfa1a1ba5da0af3787e00579`.
Its SHA-256 is
`a1f7a3562c743eab602cf98f6380339c63aa3824448380e570b1dcbbb3e450b3`.
The existing provenance TSV preserves paths and hashes back to the earlier
local research snapshot.

Identical bytes alone do not establish the original author or copying
direction. The initial review did not establish applicable terms from the
notices at the old pin. The [subsequent file-specific investigation](provenance/fastexp.md)
identified identical bytes in a later official revision that explicitly declares
`CC0-1.0 OR Apache-2.0`. That later licensed distribution is the basis recorded
for this exact file; no retroactive license on the old pin or coverage of all
support files is asserted. The CC0 notice in the separate `crypto-specs`
repository is not automatically applied to Formosa's `proof/eclib`. This
provenance note does not modify the original support theories, historical TSV,
or proof hashes.
