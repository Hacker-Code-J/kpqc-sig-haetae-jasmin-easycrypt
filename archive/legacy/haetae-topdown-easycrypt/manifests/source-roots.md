# Source roots and precedence

All paths are relative to the repository root and are read-only inputs to this
sprint.

| Priority | Root | Role | Trust boundary |
| --- | --- | --- | --- |
| 1 | `CryptoLab_HAETAE.pdf` | official algorithm specification | pinned PDF; byte-identical to current v260204 security copy |
| 2 | `haetae-ref-jasmin/` | implementation under verification | source to extract; extraction is not correctness |
| 3 | `haetae-ref-easycrypt/` | existing functional/security evidence | reuse only exact compiled propositions and premises |
| 4 | `haetae-ntt-verify/easycrypt*/` | NTT foundation | verify linkage to current `hpoly.jazz`; not whole API |
| 5 | `haetae-security/` | conditional paper security model | compiled does not mean paper-faithful or non-vacuous |
| 6 | `mldsa-easycrypt/`, `mldsa-jasmin/` | pattern reference | no HAETAE theorem import; license and semantic differences apply |
| 7 | `easycrypt/` | local tool/support material | auxiliary, not a proof target by location alone |

No existing file was copied into this project.  The adapter theories import
existing theories in place.  Focused generated extraction is created only in a
temporary directory and is reproducible from pinned source.

## Specification identity

- `CryptoLab_HAETAE.pdf`: SHA-256
  `80d28b3af9af2a27dba0eb4746f9b5755e05cb9a86bb6596f45fda06c605f3f6`.
- `haetae-security/HAETAE_v260204.pdf`: same SHA-256.
- Metadata: 46 pages, creation/modification 2026-02-04 15:55:59 KST,
  PDF 1.7, 445450 bytes.
- Other dated PDFs are different; no theorem is silently moved between them.

## HAETAE-2 parameters read from the PDF

`n=256`, `(k,l)=(2,4)`, `q=64513`, `eta=1`, `tau=58`, `gamma=48.858`,
key-acceptance probability `0.1`, expected repeats `6.0`, `B=9846.02`,
`B'=9838.98`, `B''=12777.52`, `alpha=256`, `alpha_h=512`.

## ML-DSA semantic firewall

ML-DSA is not a drop-in HAETAE spec.  Its FIPS-204 modulus (`8380417`),
module dimensions/parameter sets, bounded samplers, rejection equations, hint
format, challenge encoding, and packing differ.  HAETAE additionally uses its
own hyperball/bimodal construction, singularity/fixed-point path, and transcript
layout.  Structural patterns may be read, never imported as correctness facts.

## Week 7 focused implementation roots

The signature-codec extraction reads
`haetae-ref-jasmin/jasmin/signature_pack.jazz` and
`signature_unpack.jazz` plus their pinned `.jinc` dependencies. The selected
standalone roots are `pack_sig_mode2_full_jazz` and
`unpack_sig_mode2_full_jazz`; their closures include the actual prefix and
suffix helpers. Exact source and generated hashes are in `sources.sha256` and
`generated-extractions.sha256`.

## Week 8/9 HBZ rANS roots

The rANS focused extraction reads the pinned `hpoly.jazz`, `encoding.jazz`,
`encoding.jinc`, `sparse_encoding.jinc`, and `encoding_tables.jinc` sources.
Week 9 reuses the Week 8 generated closures for `rans_encode_jazz`,
`rans_decode_jazz`, and `encode_hb_z1_mode2_full_jazz`; it adds no copied
source and no new trust root. The actual procedures used by the unary harness
are `_rans_encode`, `__copy_encoded_suffix`, and `_rans_decode` from those
closures.

## Week 10 encoder-only root

Week 10 adds no source root. It reuses the pinned `rans_encode_jazz` closure
from `hpoly.jazz` and the literal mode-2 table arrays already extracted in
Week 8. The direct target is `RansEncodeTarget.M._rans_encode`; deterministic
regeneration and the existing generated hash remain mandatory. No decoder or
full-wrapper source is newly trusted by the Week 10 claim.

## Week 11/12 encoder and decoder roots

Weeks 11 and 12 add no source roots. Week 11 reuses the pinned
`rans_encode_jazz` closure; Week 12 reuses the pinned `rans_decode_jazz`
closure, both from `haetae-ref-jasmin/jasmin/hpoly.jazz`. Their direct targets
are `RansEncodeTarget.M._rans_encode` and
`RansDecodeTarget.M._rans_decode`. Deterministic regeneration, generated hashes
and concrete table-certificate regeneration remain mandatory. The new Week 12
theories are authored refinements inside this project, not new trusted inputs.
