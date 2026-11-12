# Thesis–artifact map

This table indexes the implementations, theorems, and verification commands
supporting the research claims. A theorem's presence in a file is distinct from
having rechecked it against the current public sources. Consult the
[validation record](../haetae-easycrypt/VALIDATION.md) and the source hashes and
target inventory for the corresponding run.

The thesis identifiers are LaTeX labels in the current manuscript. Labels are
used instead of chapter, section, or theorem numbers so that claims remain
identifiable when numbering changes. This does not mean that the manuscript
or final publication metadata is included in this repository. This repository
covers HAETAE; the thesis's NTRU+ results are not included here.

## Claims and proofs

In the paths below, `E` means `haetae-easycrypt` and `H` means
`haetae-hardened`. The table links to the actual files and names representative
public theorems. Reading only a representative theorem can omit dependency
proofs or premise checks, so use the verifier for reproduction.

| Thesis claim or label | Implementation or model | Representative theorem and file | Scope and premises | Reproduction |
| --- | --- | --- | --- | --- |
| HAETAE NTT multiplication, `thm:haetae-ntt-composition` | `poly_ntt_jazz`, pointwise multiplication, `poly_invntt_jazz` | [`NTTCompositionInstance.ec`](../haetae-easycrypt/proofs/NTTCompositionInstance.ec): `haetae_ntt_product_total` | Composition including coefficient representations, ranges, and Montgomery scaling; see the [arithmetic assumptions](../haetae-easycrypt/manifests/ntt-assumptions.md) | N |
| Connection to actual challenge-polynomial and matrix products, `sec:haetae-ntt-composition` | `sign_compute_cs2_jazz`, `keypair_m23_matrix_jazz`, `keypair_m5_matrix_jazz` | [`NTTProductCorrectness.ec`](../haetae-easycrypt/proofs/NTTProductCorrectness.ec): `sign_compute_cs2_total`; [`NTTMatrixProductCorrectness.ec`](../haetae-easycrypt/proofs/NTTMatrixProductCorrectness.ec): `matrix_m23_export_total`, `matrix_m5_export_total` | Calls satisfying the array-size, representation, and coefficient-range contracts | N |
| Gaussian candidate arithmetic, `prop:gaussian-candidate-contracts` | `sample_gauss83_jazz`, `approx_exp_jazz`, sigma76 path | [`CDTCorrectness.ec`](../haetae-easycrypt/proofs/CDTCorrectness.ec): `sample_gauss83_jazz_total`; [`ApproxExpNumericalCorrectness.ec`](../haetae-easycrypt/proofs/ApproxExpNumericalCorrectness.ec): `sigma76_approx_exp_numerical_total` | Integer/word computations and termination, including the exponential approximation's input interval and rounding | E |
| CDT and reference Gaussian distribution, `sec:gaussian-correctness` | Uniform 83-bit input experiment | [`CDTGaussianApproximation.ec`](../haetae-easycrypt/proofs/CDTGaussianApproximation.ec): `uniform83_jasmin_half_gaussian_error` | Statistical distance `<2^-78` from the nonnegative discrete Gaussian; not a statement about a concrete SHAKE distribution | E |
| Signed buffer output, `prop:gaussian-signed` | iid byte, carry, and sign model with the actual consumer | [`GaussianSignedCorrectness.ec`](../haetae-easycrypt/proofs/GaussianSignedCorrectness.ec): `gsc_actual_gaussian_event` | Distance `<2^-31` for 256 signed integer observations under `gib_bounds n offset signoff`; signed32 storage semantics require a separate fit condition | E |
| Rejection rate and expected candidate attempts, `sec:gaussian-rejection-counts` | `SigmaJoint203Experiment`, independent candidate retries | [`GaussianAcceptanceActual.ec`](../haetae-hardened/easycrypt/proofs/GaussianAcceptanceActual.ec): `gaa_extracted_rejection`; [`GaussianAttemptExpectation.ec`](../haetae-hardened/easycrypt/proofs/GaussianAttemptExpectation.ec): `gae_actual_expected_count_bound` | Average rejection rate `<1/20`, expected candidate count through success `<20/19`; distinct from a lower bound for each fixed candidate or the cost of Hyperball's outer loop | G |
| Counterexamples to the original radius check, `sec:hyperball-witnesses` | Actual Gaussian consumer, Newton, scale, and norm calls | [`HyperballWitnessReplay.ec`](../haetae-easycrypt/proofs/HyperballWitnessReplay.ec): `hbwr_accepted_outside_radius_total` | Acceptance and integer-radius violation for constructed candidate sequences; no claim of a corresponding SHAKE seed or its reachability | E, W |
| Radius-violation probability in one original attempt, `prop:hyperball-unsafe-attempt` | `HyperballIidAttempt.sample` | [`HyperballIidAttemptSafety.ec`](../haetae-easycrypt/proofs/HyperballIidAttemptSafety.ec): `hia_accepted_outside_bound`, `hia_terminates` | Joint event of acceptance AND radius violation in one iid attempt; distinct from conditioning on acceptance or bounding the outer loop | E |
| Total correctness of the hardened decision, `prop:checked-acceptance` | `_hb_checked_scale_and_check_values` | [`CheckedAcceptanceCorrectness.ec`](../haetae-hardened/easycrypt/proofs/CheckedAcceptanceCorrectness.ec): `hca_scale_and_check_total` | Always terminates under the array-length contract; acceptance implies actual integer sum of squares ≤ the bound, without a prior no-overflow assumption | H |
| Actual hardened return paths, `prop:checked-production` | Signing, standalone Hyperball, and public phase paths | [`CheckedProductionCorrectness.ec`](../haetae-hardened/easycrypt/proofs/CheckedProductionCorrectness.ec): `hpc_signer_full_safe`, `hpc_standalone_full_safe` | Safety of returning executions of the complete Hyperball function; excludes termination of the outer loop | H, W |
| Rényi comparison for the exponential approximation and one-attempt output | Exact-exponential reference, hardened candidate and acceptance bit | [`GaussianRenyiProduction.ec`](../haetae-hardened/easycrypt/proofs/GaussianRenyiProduction.ec): `grp_renyi_bounds`; [`HyperballRenyiProduction.ec`](../haetae-hardened/easycrypt/proofs/HyperballRenyiProduction.ec): `hrf_common_bound` | Integer orders 2–1024 under the stated iid one-attempt law; does not automatically extend to the full ideal mask, acceptance-conditioned distribution, or UF-CMA | R |
| CT/SCT disclosure policy, `sec:haetae-implementation-security` | Hardened arithmetic checks and explicit declassification | [`check-ct.sh`](../haetae-hardened/scripts/check-ct.sh) | Results relative to the checker, selected functions, and permitted disclosures | C |

The Rényi row locates the related research proofs. It does not replace the
remaining obligations for the final signature-security composition described
in the manuscript's `sec:haetae-security-composition`. API-related proofs are
also distinct from a proof of the complete API. For example,
[`ProductionApiCorrectness.ec`](../haetae-easycrypt/proofs/ProductionApiCorrectness.ec)
covers contracts for memory helpers such as copying and initialization.

## Reproduction commands

Run these commands from the repository root after activating the environment
as described in the [environment guide](../env/README.md). Use
`bash scripts/reproduce.sh full` for the complete bundle of checks. Checking
individual proof files does not replace rechecking all dependency proofs.
Before running hardened commands individually, materialize the implementation
under verification with `python3 haetae-hardened/scripts/materialize.py`.

| Code | Command |
| --- | --- |
| E | `make -C haetae-easycrypt verify-new` |
| N | `make -C haetae-easycrypt verify-ntt` |
| H | `python3 haetae-hardened/scripts/verify.py --group all` |
| G | `python3 haetae-hardened/scripts/verify.py --group gaussian-rate` |
| R | `python3 haetae-hardened/scripts/verify.py --group gaussian-renyi` and `--group hyperball-renyi` |
| W | `make -C haetae-easycrypt test-hyperball-boundary`; for the hardened variant, run `make -C haetae-jasmin libs` and `make -C haetae-hardened libs`, then `python3 haetae-hardened/tests/checked-hyperball.py` |
| C | `bash haetae-hardened/scripts/check-ct.sh` |

Finite execution checks for the official KAT, signing, API, and interoperability
are reproduced with `make -C haetae-jasmin test` and
`make -C haetae-hardened test`. These results do not replace the premises of
the theorems above or a complete cryptographic security proof.

## Common trust boundaries

- Program theorems concern the Jasmin extraction model and the stated array
  and pointer contracts. Native execution with arbitrary pointers, the entire
  ABI, and correctness of the compiler and verifier themselves are separate boundaries.
- Distinguish iid distribution results from concrete seeded SHAKE execution.
  Partial correctness concerns executions that terminate; termination theorems
  apply only under their stated models and premises.
- Read the [original implementation's detailed scope](../haetae-easycrypt/CLAIMS.md)
  together with the [hardened variant's scope](../haetae-hardened/README.md).
- Freeze this map together with the actual verification targets and source
  hashes for each release. Adding research files does not increase the target
  count or successful coverage of an earlier execution record.
