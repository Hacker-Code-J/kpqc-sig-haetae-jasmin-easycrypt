# Review Checklist: Jasmin NTT Verification Methodology Paper

Scope: `paper/jasmin_ntt_verification_methodology.tex` should read as an
analysis paper on using the Jasmin toolchain to verify safety, regular
constant-time, speculative constant-time, and source-to-assembly correspondence
for the scalar HAETAE NTT artifact.

## Checklist

- [ ] Analysis-paper framing
  - The title, abstract, introduction, and conclusion make the paper an
    analysis of Jasmin-based verification, not only a command log.
  - The paper explains why each checker result is meaningful.

- [ ] NTT implementation context
  - The checked routines are named.
  - The file structure (`hpoly.jazz`, `poly.jinc`, `reduce.jinc`,
    `params.jinc`, `zetas.jinc`) is explained.
  - Stage-specialized NTT/inverse-NTT helpers and base multiplication are
    described enough to identify what is being checked.

- [ ] Safety-checking accuracy
  - The paper follows `~/jasmin/docs/source/tools/safety_checker.md`.
  - Safety is defined as well-defined semantics, not merely "no crash".
  - The paper states that memory validity and alignment remain caller/ABI
    preconditions for pointer arguments.
  - The actual `paper/logs/jasmin-checksafety.log` output is analyzed.

- [ ] Regular constant-time accuracy
  - The paper follows `~/jasmin/docs/source/tools/ct.md`.
  - It describes public/secret typing, public branch conditions, public memory
    addresses/array indices, and the prior-safety assumption.
  - It explains why an empty `paper/logs/jasmin-ct.log` is evidence only with a
    successful command exit.

- [ ] Speculative constant-time accuracy
  - The paper follows `~/jasmin/docs/source/tools/sct.md`.
  - SCT is described as Jasmin's SCT/Spectre-v1/selective-SLH-style checker
    model, not all speculative or physical leakage.
  - The paper analyzes the exported transient-pointer to public-pointer
    security types in `paper/logs/jasmin-ct-speculative.log`.
  - The wrapper `#init_msf` and generated `lfence` evidence are connected.

- [ ] Claim separation
  - Safety, regular CT, SCT, source-to-assembly correspondence, functional
    correctness, and cryptographic security are separate claims.
  - Functional correctness of the NTT and HAETAE security are explicit
    non-claims.
  - Full physical side-channel security and all microarchitectural leakage are
    explicit non-claims.

- [ ] Documentation basis
  - The paper uses the home-directory Jasmin documentation as the current
    documentation basis without embedding machine-local paths.
  - Bibliography metadata remains portable.

- [ ] Verification-log analysis
  - The paper analyzes actual logs in `paper/logs/`, not only expected
    commands.
  - It includes tool version, source revision, safety result, CT result, SCT
    result, compile result, assembly diff result, and hash comparison.

- [ ] Limitations and invalidation criteria
  - The paper states when evidence must be regenerated.
  - It identifies changes that require manual leakage review.

- [ ] Portability and build quality
  - The paper and bibliography do not contain `/home/...` or `~/jasmin/...`.
  - The PDF builds with BibTeX and LaTeX.
  - The final LaTeX log has no errors, unresolved citations, unresolved
    references, rerun requests, package errors, or overfull boxes.

## Review Result Before This Revision

Mostly satisfied, with three weaknesses:

1. **Analysis-paper framing was present but diluted by the "methodology" title
   and by placing results under "Reproducibility Record".**
   The paper explained commands well, but a reviewer could still read it as an
   artifact report rather than an analysis paper.

2. **The result interpretation needed a more explicit transition from raw logs
   to analysis claims.**
   The paper had a results-analysis subsection, but it should be elevated and
   tied more directly to the claim structure.

3. **The link between the home-directory Jasmin docs and the paper's checker
   semantics needed to be made clearer without adding machine-local paths.**
   The paper cited `JasminDocs`, but the checklist requires explicit review
   against the requested documentation categories.

## Revision Plan

- Retitle and reframe the paper as an analysis paper.
- Promote log interpretation from a subsection of reproducibility to a section
  named "Analysis of Verification Results".
- Add an explicit paragraph connecting the home-directory Jasmin documentation
  categories to the checker semantics used in the paper.
- Rebuild and verify the LaTeX log.

## Post-Revision Status

- [x] Analysis-paper framing strengthened in the title, abstract, introduction, and conclusion.
- [x] NTT implementation context remains present through file-structure, wrapper, stage-helper, and base-multiplication discussion.
- [x] Safety-checking semantics and caller preconditions are tied to the Jasmin safety-checker documentation and to `jasmin-checksafety.log`.
- [x] Regular CT semantics are tied to the Jasmin CT documentation and to the empty successful `jasmin-ct.log`.
- [x] SCT semantics are tied to the Jasmin SCT documentation, exported wrapper types, `#init_msf`, and generated `lfence` evidence.
- [x] Claim boundaries separate safety, CT, SCT, assembly correspondence, functional correctness, cryptographic security, and physical leakage.
- [x] Home-directory Jasmin documentation is cited through a portable bibliography entry without embedding machine-local paths.
- [x] Actual verification logs are analyzed in the paper.
- [x] Evidence invalidation criteria are stated.
- [x] Final build/log status: BibTeX and LaTeX rebuild completed; final log scan found no LaTeX errors, unresolved citations, unresolved references, rerun requests, package errors, or overfull boxes.
