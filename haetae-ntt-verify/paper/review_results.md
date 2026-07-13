# Review Results for `jasmin_safety_ct.tex`

Date: 2026-05-21

## Verdict

The draft is a good artifact-centered note for the safety, regular constant-time, and speculative constant-time checks of the scalar Jasmin HAETAE NTT code. It is not yet suitable as a complete standalone submission without revisions to scope, reproducibility, and positioning.

## Submission Blockers

1. Functional-correctness scope was too broad.
   - The paper discussed functional correctness of "the extracted scalar wrappers" without distinguishing the two NTT wrappers from base multiplication.
   - The checked EasyCrypt top-level file proves `poly_ntt_jazz` and `poly_invntt_jazz`.
   - The dissertation explicitly records that `poly_basemul_jazz` does not yet have a complete end-to-end functional correctness proof.
   - Required revision: state that base multiplication is covered here only by safety and timing checks unless a base-multiplication EasyCrypt proof is added.

2. Reproducibility evidence was too informal.
   - The draft relied on the current repository and a user-specific Jasmin checkout without recording tool versions, repository revision, or review-time outputs.
   - Verified locally:
     - `jasminc -version`: `Jasmin Compiler 2026.03.0`
     - repository revision: `f0e1399`
     - `jasminc -checksafety -o /tmp/hpoly-safe.s jasmin/hpoly.jazz`: no safety violation for all three exported routines
     - `jasmin-ct jasmin/hpoly.jazz`: passed
     - `jasmin-ct --speculative jasmin/hpoly.jazz`: passed and printed the expected transient-pointer/public-pointer/secret-value types
   - Required revision: add tool/version/revision information and recommend packaging logs with the artifact.

3. The paper's novelty and completeness framing was too narrow for a standalone submission.
   - The contribution is a checked implementation-level safety/timing argument, not a new NTT algorithm, vectorized implementation, full HAETAE implementation proof, or full protocol security proof.
   - Required revision: make this narrow claim explicit and position the paper as an artifact/paper about closing the compiler-side layer below existing functional proofs.

## Correctness and Presentation Issues

1. Wrapper listing was incomplete.
   - The listing omitted `poly_invntt_jazz`, although the paper repeatedly claims three exported routines.
   - Required revision: include the inverse wrapper or mark the listing as explicitly partial.

2. Source-file count was inconsistent.
   - The paper said the artifact consists of four files, then relied on `params.jinc`.
   - Required revision: list `params.jinc` as a fifth source/support file or explicitly call it a shared include.

3. Source-to-assembly wording needed precision.
   - The paper should distinguish the formal source checks, Jasmin compiler preservation discipline, and light assembly-shape inspection.
   - Required revision: weaken "guarantee" wording where necessary and state the assumed Jasmin preservation layer.

4. Related work was too short.
   - Required revision: explain how this work differs from Jasmin's general verification methodology and Kyber/Dilithium-style implementation verification.

## Applied Revision Plan

- Add this review record under `paper/`.
- Patch `paper/jasmin_safety_ct.tex` to:
  - add `params.jinc` to the artifact table;
  - include all three exported wrappers in the wrapper listing;
  - record the reproduced toolchain version, repository revision, and command outcomes;
  - clarify that EasyCrypt functional correctness currently covers forward/inverse NTT wrappers, not base multiplication;
  - refine source-to-assembly wording;
  - expand related-work/positioning text.

## Remaining Risks After Revision

- The paper still needs an artifact bundle with machine-readable logs for a real submission.
- A standalone submission may still be considered too narrow unless submitted to an artifact, short-paper, or verification-experience venue, or expanded with functional correctness integration.
- Base multiplication remains a gap for any claim about complete polynomial multiplication or full HAETAE arithmetic correctness.

## Additional Review Against the 2026 Jasmin Material

Sources used:

- `dissertation/2026_Jasmin.pdf`, treated as the baseline as requested.
- `dissertation/2511.11292v1.pdf`.
- `dissertation/The Last Mile.pdf`.
- `dissertation/2021_Jasmin.pdf`.
- `dissertation/2023_Jasmin.pdf`.
- `dissertation/2024_Jasmin.pdf`.

Verdict: the English draft is substantially stronger than the original review target, especially in its NTT implementation narrative and its explanation of the safety, regular CT, and speculative CT checks. It is still not ready as a complete standalone submission. It is close to an artifact or short experience paper, but a full-paper submission needs fixes to portability, citation coverage, and the exact scope of the Jasmin guarantees.

### Findings

1. Submission-blocking portability problem: the draft contains machine-local paths.
   - Location: `paper/jasmin_safety_ct.tex`, lines 551-563 and 579-591.
   - The paper named an absolute user-local documentation path and user-specific Jasmin compiler paths as evidence sources.
   - This is not acceptable in an anonymous or archival submission. Replace these with a packaged artifact path, a container image, a repository commit, or public Jasmin documentation references. If local paths remain useful to authors, put them only in an internal artifact README.
   - The LaTeX log also reports several underfull boxes in this paragraph, so the portability issue is visible typographically.

2. Major citation and positioning gap: the required recent Jasmin sources are not cited.
   - Location: `paper/refs.bib`, lines 21-32; `paper/jasmin_safety_ct.tex`, lines 443-452, 767-778, and 900-929.
   - The draft still cites mainly the 2017 Jasmin paper for the framework-level claims. It does not cite the 2026 slide deck, "The Last Mile", the 2021/2023/2024 Jasmin slides, or the 2025 compiler-security paper.
   - The 2026 slides emphasize the current model: source-level CT, public branch conditions and memory indices, compiler preservation of CT, current safety-check workflow, and the newer auto-spill discussion. The draft should explicitly say which parts follow the 2026 state of Jasmin and which parts are older background.
   - The 2511.11292v1 paper is especially important if the draft mentions cryptographic-security preservation. That paper covers the compiler front-end for KEM IND-CCA preservation and explicitly leaves the back-end and side-channel-adversary integration outside its main formalization. The present paper should not imply that this result directly proves full source-to-assembly cryptographic security for HAETAE signatures.

3. Major scope issue: the compiler-level guarantee needs tighter separation of CT preservation, safety, and cryptographic-security preservation.
   - Location: `paper/jasmin_safety_ct.tex`, lines 71-75, 642-654, 767-778, 900-929, and 1054-1060.
   - The 2026 slides support the statement that Jasmin is designed to preserve semantics and CT, and that branch conditions and memory indices must be public. However, the newest compiler-security paper is narrower than the language in some parts of the draft might suggest: it proves front-end cryptographic-security preservation for KEMs, not a complete back-end or side-channel theorem.
   - Recommended revision: add an explicit "which theorem is used where" paragraph. Use the CT-preservation line for the timing trace claim, use safety checker output for defined execution under pointer preconditions, and keep the 2511 result as related work unless the paper actually instantiates its KEM theorem.

4. Major SCT-model qualification: the speculative claim should name its exact model and exclusions.
   - Location: `paper/jasmin_safety_ct.tex`, lines 531-549 and 872-898.
   - The draft explains the `sct` annotations and `#init_msf()` well, but line 897 says the only required speculation boundary is at the exported entry point. That is true only relative to the checker model and this call graph. It should not read as a claim about all speculative-execution effects.
   - Recommended revision: state that the claim is Jasmin SCT/Spectre-v1-style selective hardening for this source, with no independent measurement claim and no broad claim for all Spectre variants or microarchitectural channels.

5. Major reproducibility gap: the draft reports checks, but the artifact still lacks raw checker logs.
   - Location: `paper/jasmin_safety_ct.tex`, lines 932-968.
   - The table is useful, but a reviewer needs raw `jasminc -checksafety`, `jasmin-ct`, `jasmin-ct --speculative`, compiler version, and assembly comparison logs. The paper itself even says these should be included.
   - Required before submission: add a versioned `paper/logs/` or artifact `logs/` directory and cite it from the paper.

6. Major completeness issue for a full paper: the result remains too narrow unless the venue accepts artifact reports.
   - Location: `paper/jasmin_safety_ct.tex`, lines 75-78, 119-127, and 1000-1020.
   - The draft correctly says base multiplication lacks the complete EasyCrypt functional proof. That honesty is good, but it means the paper is not yet a complete implementation-correctness paper for HAETAE polynomial arithmetic.
   - For a full paper, add at least one of: a full base-multiplication proof, an end-to-end integration theorem, a stronger comparison/evaluation section, or a clear artifact-evaluation venue framing.

7. Moderate accuracy issue: typed pointer wording should not obscure caller preconditions.
   - Location: `paper/jasmin_safety_ct.tex`, lines 220-230.
   - The phrase that the declaration "gives the safety checker a typed 256-word memory region" can be read too strongly. The type gives a shape and index discipline; validity, allocation, and alignment are still preconditions on the initial state.
   - Later sections state the conditional reading correctly. Make the early wording match that conditional story.

8. Moderate 2026-alignment issue: the old safety checker is presented without the 2026 caveat.
   - Location: `paper/jasmin_safety_ct.tex`, lines 454-496 and 697-719.
   - The 2026 slides present `jasminc -checksafety` as the old static safety checker: valuable, but sometimes slow, non-modular, and incomplete for safe code. They also present a newer modular workflow with safety contracts/assertions and EasyCrypt discharge.
   - Recommended revision: explain that this artifact intentionally uses the old checker because the scalar, stage-specialized code fits it. That makes the use of `-checksafety` look principled rather than dated.

9. Minor presentation issue: the Korean draft likely inherits the same artifact-path and citation problems.
   - Location: `paper/jasmin_safety_ct_ko.tex`, especially the local-documentation paragraph.
   - If both versions will be submitted or distributed, apply the same portability and citation fixes to the Korean version.

### Current Build Status

- `paper/jasmin_safety_ct.pdf` builds to 11 pages.
- The English LaTeX log has underfull boxes but no unresolved references, unresolved citations, LaTeX errors, or overfull boxes in the latest checked log.
- `paper/jasmin_safety_ct_ko.pdf` builds to 10 pages.
- The Korean LaTeX log has the existing `microtype`/KoTeX warning and underfull boxes, but no unresolved references, unresolved citations, LaTeX errors, or overfull boxes in the latest checked log.

## Revision Applied After 2026 Jasmin Review

Date: 2026-05-21

Fixed:

- Removed machine-local paths from both `paper/jasmin_safety_ct.tex` and `paper/jasmin_safety_ct_ko.tex`.
- Added bibliography entries and citations for `2026_Jasmin.pdf`, `2511.11292v1.pdf`, `The Last Mile.pdf`, and the 2021/2023/2024 Jasmin slide decks.
- Reworked the claim structure so safety checking, regular CT checking, SCT checking, compiler CT preservation, and front-end cryptographic-security preservation are separate statements.
- Qualified SCT as evidence in the Jasmin Spectre-v1-style SCT checker model, not as a claim about every speculative-execution or microarchitectural channel.
- Clarified that typed pointers provide array shape and index discipline, while validity, allocation, and alignment remain initial-state/caller preconditions.
- Explained why this artifact intentionally uses `jasminc -checksafety` even though the 2026 Jasmin material presents a newer modular safety workflow.
- Added raw reproducibility logs under `paper/logs/`, including checker outputs, compiler version, repository revision, and assembly comparison evidence.
- Mirrored the same substantive revisions in the Korean version in natural academic Korean.

Remaining risks:

- A submitted artifact should still identify the exact Jasmin compiler source checkout or container image corresponding to `Jasmin Compiler 2026.03.0`.
- The paper remains narrow: base multiplication still lacks a complete EasyCrypt functional-correctness proof, and the work does not prove full HAETAE signature security.
- The SCT claim remains model-relative, as stated in the revised paper.
- Final readiness depends on the target venue's page limit and whether an artifact/experience-style contribution is acceptable.

## Overall Structure and Accuracy Re-evaluation

Date: 2026-05-21

Top three remaining weaknesses selected for supplementation:

1. Claim boundaries were accurate but too dispersed.
   - Risk: a reviewer could still conflate safety checking, CT/SCT checking, compiler preservation, EasyCrypt functional correctness, and full cryptographic security.
   - Supplement applied: added a claim-boundary table near the introduction in both English and Korean versions, explicitly pairing each claim area with its evidence and non-claims.

2. The paper lacked enough mathematical/functional context before the implementation walkthrough.
   - Risk: the text described the Jasmin code well, but a standalone reader had to infer the HAETAE NTT target, bit-reversed spectral order, Montgomery table convention, and difference from MLKEM/Kyber from later or external material.
   - Supplement applied: added an algorithmic and functional context subsection to both versions, defining the negacyclic ring, primitive root, full 256-point NTT formula, inverse scaling, and concrete Montgomery table layout.

3. The verification evidence was present but not summarized at the raw-artifact level.
   - Risk: the evidence section listed commands and logs, but did not give a compact reviewer-facing map from raw files to the claims they support.
   - Supplement applied: added a raw-evidence table to both versions, tying `jasmin-checksafety.log`, `jasmin-ct-speculative.log`, `hpoly.s`, and assembly comparison logs to the paper's safety, SCT, and source-to-assembly claims.

Remaining risk after this pass:

- The contribution is still best framed as an artifact/experience or focused verification paper unless the target venue accepts a narrow compiler-side safety/timing result.
- Page length may increase after the added tables and mathematical context; final suitability still depends on venue limits.

## Second Structure and Accuracy Pass

Date: 2026-05-21

Top three remaining weaknesses selected for this pass:

1. Contribution and organization were still implicit.
   - Risk: after several technical additions, the introduction explained the claim boundary but did not give a compact contribution list or paper roadmap.
   - Supplement applied: added a three-part contribution statement and section roadmap to both English and Korean versions.

2. The functional-correctness interface for the helperized source needed a sharper statement.
   - Risk: the paper said the companion EasyCrypt development proves the forward and inverse wrappers, but did not explain why that proof applies to the helperized full-safe source checked by Jasmin rather than only to an older direct-loop model.
   - Supplement applied: added the EasyCrypt bridge chain `Hpoly_extract.ec -> CTLoopEquiv.ec -> Hpoly_loop.ec -> NTT_Fq.ec -> NTTFullSpec.ec/NTTFullAlgebra.ec -> NTTEndToEnd.ec`, while preserving the limitation that base multiplication is not functionally proved.

3. Reproducibility still lacked an explicit reviewer recipe.
   - Risk: listing logs is useful, but a reviewer benefits from a minimal command sequence and expected outcomes.
   - Supplement applied: added a four-step reproduction procedure: record tool/source versions, run safety/CT/SCT checks, regenerate assembly, and compare `hpoly.s` by hash and diff.

Remaining risk after this pass:

- The added roadmap and proof-interface text improve standalone readability, but the paper remains narrow unless positioned as a focused verification artifact.
- Further expansion should be weighed against page limits; the next highest-value content would be a small performance/evaluation table or a completed base-multiplication functional proof.

## Third Structure and Accuracy Pass

Date: 2026-05-21

Top three remaining weaknesses selected for this pass:

1. The threat and leakage model was still implicit across several sections.
   - Risk: readers could mistake the Jasmin CT/SCT model for a claim about all physical or microarchitectural leakage.
   - Supplement applied: added a dedicated threat-and-leakage-model subsection to both English and Korean versions, stating public inputs, secret state, checker observables, the exact coefficient-trace invariant, and exclusions such as power, EM, frequency, replacement-policy state, and checker-unmodeled prefetch behavior.

2. The evaluation surface lacked a compact size-and-scope summary.
   - Risk: the paper had verification commands and raw logs, but did not quickly show the amount of source, assembly, and log evidence actually covered by the claims.
   - Supplement applied: added an artifact-size and checked-surface table to both versions, covering constants/tables, arithmetic helpers, polynomial kernels, ABI wrappers, generated assembly, and raw verification logs. The table is explicitly framed as an audit summary, not a runtime benchmark.

3. The paper did not state when the recorded evidence becomes stale.
   - Risk: reviewers or later maintainers might edit Jasmin source, generated assembly, compiler version, annotations, or leakage-relevant constructs while still citing the old logs.
   - Supplement applied: added evidence-invalidation criteria to both versions, requiring regenerated safety, CT, SCT, and assembly-comparison logs after source, compiler, or assembly changes, and requiring renewed leakage review after raw memory operations, data-dependent branches, declassification, or new unannotated wrappers.

Remaining risk after this pass:

- The paper now states the checked surface more clearly, but it still does not include runtime performance measurements.
- The base-multiplication kernel remains safety/CT/SCT checked but not covered by the companion end-to-end EasyCrypt functional proof.

## Fourth Structure and Accuracy Pass

Date: 2026-05-21

Top three remaining weaknesses selected for this pass:

1. The abstract still compressed source-level checks, compiler preservation, and assembly evidence into one sentence.
   - Risk: readers could over-read the abstract as claiming an independent assembly proof or complete physical side-channel coverage.
   - Supplement applied: revised both abstracts to mention byte-for-byte regeneration evidence for `hpoly.s` and to state that the claim is not an independent proof of arbitrary assembly or all physical side channels.

2. The compiler-preservation step was accurate but still too prose-like.
   - Risk: a reviewer could miss the exact premises needed to move from source checks to the submitted assembly.
   - Supplement applied: added an explicit artifact-theorem schema in both versions: safety check, CT check, SCT check, Jasmin compilation, and byte-for-byte assembly equality are the premises; the conclusion is conditional and does not apply to hand-edited assembly.

3. The conclusion did not state the paper's best submission positioning.
   - Risk: the paper could be misframed as a complete implementation-correctness paper for all HAETAE polynomial arithmetic.
   - Supplement applied: added a conclusion paragraph in both versions positioning the draft as a focused verification-artifact paper and naming the additions required for a full implementation-correctness paper: base-multiplication functional proof, full integration theorem, and performance comparison.

Remaining risk after this pass:

- The paper is now structurally honest about its contribution, but venue fit still depends on whether a focused verification artifact is acceptable.
- The missing runtime comparison and base-multiplication functional proof remain the main gaps for a broader systems or full-correctness venue.
