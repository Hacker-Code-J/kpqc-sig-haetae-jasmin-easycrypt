# Security Theorem Premise Audit

This audit inventories the explicit premises of every exported lemma whose
name starts with `euf_cma_security` in
`../../haetae-security/provable-security/easycrypt/HAETAE_Security.ec`. The
machine-readable inventory is `../manifests/theorem-premises.csv`.

## Inventory result

The source currently exports 25 such lemmas with 104 explicit premises. The
104 rows are not 104 independent assumptions: later lemmas specialize or
compose earlier lemmas and therefore repeat the same premise families.

| Classification | Rows | Interpretation |
| --- | ---: | --- |
| `retained hardness/ROM` | 50 | The MLWE and Module-SIS advantage bounds repeated across 25 theorem variants. These may remain only after their games and parameters are made exactly HAETAE-specific. |
| `checked derived premise` | 5 | Two structural interface facts with a checked discharge and three sampling-hop facts with checked but deliberately coarse discharges. |
| `structural correspondence obligation` | 49 | Conditional game hops or distributional correspondences that cannot remain as assumptions of a paper-faithful theorem. |
| `implementation refinement obligation` | 0 | No exported security theorem mentions the target Jasmin implementation. This missing composition layer is itself a blocker; it is not disguised as an EasyCrypt premise. |

Status meanings are:

- `RETAINED`: a precisely stated cryptographic hardness assumption intended to
  remain visible in the final theorem;
- `CHECKED_STRUCTURAL`: discharged in EasyCrypt for the current structural
  model but not yet a paper-correspondence result;
- `CHECKED_COARSE`: discharged in EasyCrypt by a bound too weak to support the
  intended concrete security claim; and
- `OPEN`: an explicit theorem input that still needs a paper-faithful proof.

## Dependency chain

The theorem family progressively exposes and then partially discharges this
chain:

1. `euf_cma_security` accepts the Fiat-Shamir-with-aborts EUF-CMA-to-NMA hop,
   the NMA-to-MLWE/bimodal hop, the bimodal-to-Module-SIS hop, and two hardness
   bounds directly.
2. `euf_cma_security_from_simulated_hop` and
   `euf_cma_security_from_rom_internal_transcript_hop` move the first boundary
   through a signing simulator and a logged ROM transcript. Exact erasure is
   checked by `haetae_rom_internal_transcript_erasure_exact` in
   `HAETAE_HopGames.ec`.
3. The clear-site variants split a successful forgery into clear and bad
   programming-site events. `rom_internal_transcript_bad_forgery_counted_bound`
   supplies the counted bad-event term; the clear-site-to-NMA inequality is
   still a reduction boundary unless the structural constructed NMA is used.
4. `euf_cma_security_from_structural_nma_and_counted_bimodal` discharges that
   clear-site bridge with
   `rom_internal_transcript_clear_site_structural_nma_bound`. The result is
   checked for `ROMInternalTranscriptAsNMA`, not yet for the paper reduction.
5. The public-simulator and paper-simulator variants use checked exactness
   lemmas to expose successively more specific sampler boundaries:
   `rom_internal_nma_public_sim_exact`,
   `rom_internal_nma_public_sim_rom_paper_sim_exact`,
   `rom_internal_nma_real_signing_paper_sim_exact`, and
   `rom_internal_nma_real_signing_haetae_rejection_paper_sim_exact`.
   These exactness results concern the current structural definitions.
6. The exact-hyperball and RO-exact-hyperball variants isolate rejection
   sampling and lazy-ROM lifting. Their remaining NMA inequalities are the
   statistical proof surface needed before the forking/hardness reduction.
7. `bimodal_to_module_sis_reduction_bound` mechanically removes the generic
   bimodal-to-Module-SIS premise by instantiating
   `BimodalMSIS_As_ModuleSIS`. The current game-validity lift is checked; the
   exact paper distribution and norm handoff are not.
8. The final two premises in each advanced theorem are MLWE and Module-SIS
   hardness bounds. They are the only premise families intended to remain as
   cryptographic assumptions after all structural and implementation work is
   complete. The ROM remains a declared model assumption through the oracle
   definitions and must have exact domain/encoding correspondence even when it
   is not a standalone implication in the theorem statement.

The syntactically shortest advanced result is
`euf_cma_security_from_checked_ro_sampling_hop_and_counted_bimodal`: it has one
open RO-exact-hyperball-NMA reduction plus the two hardness bounds. Its name
must not be read as a paper-level closure claim. The preceding signing-to-RO
hop is supplied by
`real_signing_ro_exact_hyperball_hop_checked_from_loss_budget`, which ultimately
uses `rom_internal_nma_ro_signing_attempt_ro_exact_hyperball_loss_bound`. That
fallback proves the inequality from probability boundedness and
`rejection_sampling_loss_term >= 1`; it is machine-checked but gives a vacuous
statistical loss for concrete security.

The budgeted variant is a more informative future proof surface. It leaves the
unbudgeted/budgeted wrapper relations, the per-sample statistical obligation,
the query-counted NMA-to-hardness reduction, and the two hardness assumptions
explicit.

## Gap IDs used by the CSV

The source gap table predates stable identifiers. This audit assigns the
following local IDs to its row names; they refer to
`../../haetae-security/PAPER_CORRESPONDENCE_GAPS.md` and do not claim that the
gaps have been closed.

| Audit ID | Gap-table area | Required closure |
| --- | --- | --- |
| `GAP-MSIS` | Module-SIS equation | Exact HAETAE instance distribution plus extractor relation and norm bounds. |
| `GAP-PK-FIPS202` | Public key algebra and FIPS202 | Target keygen algebra plus concrete SHAKE/Jasmin byte and memory equivalence. |
| `GAP-SIGNING` | Signing equations | Real hyperball sample commitment challenge response hint and accepted-output distribution. |
| `GAP-CHALLENGE` | Challenge distribution | Full transcript encoding support cardinality point probability and min-entropy. |
| `GAP-ROM-DOMAINS` | ROM output distributions | Exact domain separation and byte encoding for every query type. |
| `GAP-REJECTION` | Rejection sampling | Exact sampling law abort checks accepted-loop distribution and non-vacuous loss. |
| `GAP-FORKING` | Forking extraction | Two accepting transcripts imply the exact bimodal self-target MSIS relation and bounds. |
| `GAP-TOP-LEVEL` | Top-level theorem | Remove every non-hardness proof-boundary premise and retain only exact hardness games plus concrete parameter/query facts. |
| `GAP-JASMIN` | No corresponding gap-table theorem row | Compose the paper model with extracted mode-2/3/5 keygen sign and verify refinements; tracked as `OBL-COMPOSE`. |

The CSV also links retained assumptions and proof obligations to the stable IDs
in `../manifests/assumptions.md`, notably `CRYPTO-MLWE`, `CRYPTO-MSIS`,
`MODEL-ROM`, and the implementation obligations.

Planned ownership is recorded separately in
`../manifests/paper-gap-owners.csv`. Every one of the eight source table rows
has a planned owner file, named future lemma, and testable acceptance criterion.
Run `../scripts/check-paper-gap-owners.sh` to verify row coverage and ensure
every gap ID used by an open theorem premise has an owner. Planned names are a
work assignment—not evidence that the lemmas exist or compile.

## What currently compiles

The Phase 0 fresh baseline compiled all 16 managed security targets with
`easycrypt compile -no-eco`, including `HAETAE_Security.ec` and
`HAETAE_HopGames.ec`. It also found no EasyCrypt `admit`, `abort`, or `axiom`
declarations in that managed surface. Evidence is recorded in
`../logs/security-fresh-summary.txt`.

That result establishes that all theorem bodies type-check and that their
displayed implications follow from their displayed premises. It does not
establish the open premises, make a coarse bound non-vacuous, align the
structural games with the HAETAE specification, or connect any game to
`haetae-ref-jasmin`.

## Blockers to a paper-faithful Jasmin theorem

A final result cannot yet be stated as “the Jasmin implementation is EUF-CMA
secure” because all of the following remain:

- replace the structural signing and rejection distributions with the exact
  HAETAE laws and prove their non-vacuous statistical hops;
- prove the exact challenge transcript encoding and ROM domain separation;
- construct the NMA/forking reduction and connect its extracted target to the
  exact HAETAE Module-SIS game;
- validate the concrete MLWE and Module-SIS game/parameter instantiations; and
- prove extracted Jasmin keygen/sign/verify refinement for modes 2 3 and 5 and
  compose those theorems with the security result.

The last item is intentionally absent from the 104 source premises because no
such implementation/security bridge theorem exists in the audited file.

## Completeness check and parser boundary

Run:

```sh
haetae-ref-easycrypt/scripts/check-theorem-premises.sh
```

The check requires exact agreement between the source and CSV keys
`(theorem, theorem line, premise ordinal, premise line)`, validates the 11-field
schema and controlled vocabularies, rejects duplicates, and pins the current
25-theorem/104-premise baseline.

This is deliberately a bounded parser rather than a general EasyCrypt parser.
It assumes that exported lemmas begin at column zero with
`lemma euf_cma_security...`, each explicit premise ends on a source line whose
last token is `=>`, theorem statements end at a column-zero `proof.`, and CSV
fields contain no commas or quoting. A formatting or grammar change must be
reviewed instead of silently accepted; the hard-coded baseline makes that
limitation fail closed.

The checker validates structural coverage and controlled classifications. It
does not prove that the English premise summaries are semantically correct or
that an open premise has been discharged. Existing discharge-lemma names are
recorded only where a checked structural/coarse lemma already exists; planned
owners for open gaps live in `paper-gap-owners.csv`.
