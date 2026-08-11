# Project scope

## In scope

- HAETAE parameter set 2 only: `n=256`, `(k,l)=(2,4)`, `q=64513`, `eta=1`,
  `tau=58`, and the mode-2 byte sizes used by the pinned implementation.
- Top-down signatures for KeyGen, Sign, Verify, end-to-end correctness,
  implementation-to-paper security composition, and the paper reduction.
- Byte-accurate refinement from the pinned Jasmin procedures to an exact
  mode-2 specification.
- Reuse of already compiled KeyGen, NTT, sampler, singularity, and FFT results
  only at their exact proposition and premise boundary.
- A security-facing adapter to the paper/ROM model, with all statistical,
  numerical, encoding, and retry losses explicit.

## Out of scope for this sprint

- parameter sets other than mode 2;
- a claim that full KeyGen, Sign, Verify, or EUF-CMA security is complete;
- physical side channels, fault attacks, RNG quality, and leakage beyond the
  explicit ideal random-tape model;
- treating memory safety or SCT/constant-time as consequences of EUF-CMA;
- modifying or repairing the existing proof trees.

Memory separation, public-pointer validity, memory safety, and SCT are tracked
as separate auxiliary obligations.  They may become premises of an API
refinement theorem, but they are not silently folded into its cryptographic
conclusion.

## Trust and version boundary

The official sprint specification is `CryptoLab_HAETAE.pdf`, SHA-256
`80d28b3af9af2a27dba0eb4746f9b5755e05cb9a86bb6596f45fda06c605f3f6`,
46 pages, produced 2026-02-04.  It is byte-identical to
`haetae-security/HAETAE_v260204.pdf`.  Older PDFs under `haetae-security/`
are distinct artifacts and are not silently substituted.

The verified implementation boundary is the pinned source under
`haetae-ref-jasmin/`; extraction success is not itself functional correctness.
The security tree is conditional evidence, not a paper-faithful end theorem,
until its premise ledger and exact scheme instance are closed.

No ML-DSA file is copied here.  `mldsa-easycrypt/LICENSE-STATUS.md` reports no
top-level license grant for the referenced Formosa proof snapshot, so it is
used only for structural reading.  It is not an imported HAETAE proof.
