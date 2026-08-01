# Assumption and Trust Register

This register separates cryptographic assumptions from idealizations,
implementation contracts, and trusted tooling. An item being listed here does
not mean it has been justified; its status states whether the project may
retain it in the final theorem.

Status vocabulary:

- `RETAINED`: expected to remain visible in the final theorem or trust statement.
- `TO_PROVE`: must be discharged by a machine-checked lemma.
- `TO_VALIDATE`: must be supported by a reproducible external check or source record.
- `EXCLUDED`: explicitly outside the resulting claim.

## Cryptographic assumptions

| ID | Assumption | Status | Required treatment |
| --- | --- | --- | --- |
| CRYPTO-MLWE | Hardness of the exact HAETAE MLWE game and parameter distribution | RETAINED | Define the game and parameters exactly; expose its advantage term in the final bound. |
| CRYPTO-MSIS | Hardness of the exact HAETAE bimodal/self-target Module-SIS game | RETAINED | Connect the forking extractor output, distribution, and norm bound to this game. |
| MODEL-ROM | HAETAE hash invocations are modeled as domain-separated random oracles | RETAINED | Prove concrete transcript/domain encodings correspond to the query types used by the games. |

## Proof obligations that are not permitted as final assumptions

| ID | Current boundary | Status | Closure criterion |
| --- | --- | --- | --- |
| OBL-PK-ALGEBRA | Structural public-key model versus real matrix/NTT/rounding/rejection computation | TO_PROVE | Extracted key generation refines the paper-faithful key-generation distribution. |
| OBL-SIGN | Structural signing fields versus hyperball sampling, commitment, challenge, responses, hints, and retries | TO_PROVE | Extracted signing refines the exact accepted signing distribution. |
| OBL-CHALLENGE | Structural challenge hash versus full encoded HAETAE transcript sampler | TO_PROVE | Support, cardinality, point probability, encoding, and min-entropy lemmas compile. |
| OBL-REJECTION | Bounded structural sampler versus exact rejection-loop distribution | TO_PROVE | Termination/losslessness and accepted-distribution/statistical-distance results compile. |
| OBL-FORK | Plumbing extractor versus exact bimodal self-target Module-SIS relation | TO_PROVE | Two-transcript extraction theorem with exact relation and norm bound compiles. |
| OBL-FIPS202 | Structural Keccak/FIPS202 model versus target Jasmin byte/memory behavior | TO_PROVE | Extracted SHAKE procedures refine concrete padding, absorb, squeeze, and encoding semantics. |
| OBL-FFT-SAFE-TRACE | Conditional rounded FFT stage semantics versus the reachable eight-round trace | TO_PROVE | Discharge every scheduled `fft_butterfly_safe_at` premise, compose the stage bridge across all eight reachable schedules, and prove global error and nonoverflow before using the score. |
| OBL-COMPOSE | Paper security theorem versus extracted public Jasmin APIs | TO_PROVE | Mode-2/3/5 implementation-security composition theorems compile. |

These obligations are grounded in
`../haetae-security/PAPER_CORRESPONDENCE_GAPS.md`; they must not be hidden as
axioms or theorem premises.

## Runtime and implementation contracts

| ID | Contract | Status | Required treatment |
| --- | --- | --- | --- |
| RUNTIME-RNG | `__jasmin_syscall_randombytes__` supplies independent, correctly distributed bytes and handles failure according to the API contract | RETAINED | State the required distribution and failure behavior; do not infer RNG quality from KATs. |
| MEMORY-PRE | Public buffers satisfy proved size, alignment, separation, and permitted-aliasing preconditions | TO_PROVE | State conditions in public refinement theorems and prove in-frame/out-of-frame behavior. |
| PARAMS | Modes 2, 3, and 5 use the specification's exact constants and serialization lengths | TO_VALIDATE | Mechanically connect `params.jinc` values to the selected specification and EasyCrypt parameters. |

## Trusted computing base

| ID | Trusted component | Status | Scope |
| --- | --- | --- | --- |
| TCB-EASYCRYPT | EasyCrypt kernel and libraries | RETAINED | Checking of definitions, tactics, and pRHL/Hoare proofs. |
| TCB-WHY3 | Why3 1.8.0 and configured solver drivers | RETAINED | Translation and orchestration of automated obligations. |
| TCB-PROVERS | Alt-Ergo 2.6.0, CVC4 1.8.0, CVC5 1.2.1, and Z3 4.12.6 as configured | RETAINED | Discharge of generated first-order obligations. |
| TCB-JASMIN2EC | Jasmin 2026.03.0 extraction semantics | RETAINED | Connection between target Jasmin source and generated EasyCrypt procedures. |
| TCB-JASMIN-COMPILER | Jasmin compiler semantic preservation | RETAINED | Needed only when lifting a source-level result to generated assembly. |
| TCB-HOST | Shell, hashing utility, build tools, and host filesystem | TO_VALIDATE | Record versions and source hashes for reproducibility; not a cryptographic assumption. |

## Explicit exclusions

| ID | Excluded claim | Status |
| --- | --- | --- |
| EX-PHYSICAL | Power, electromagnetic, cache, prefetcher, and other physical or microarchitectural leakage resistance | EXCLUDED |
| EX-FAULT | Fault-injection resistance | EXCLUDED |
| EX-RNG-QUALITY | Entropy quality of a deployment's RNG provider | EXCLUDED |
| EX-UNPINNED | Correctness or security of modified or unpinned Jasmin/specification sources | EXCLUDED |
| EX-CT | Constant-time or speculative constant-time security unless separately checked and reported | EXCLUDED |

## Maintenance rule

Every new EasyCrypt `axiom`, abstract operator used as a security premise, or
unproved premise of a top-level theorem must be added here in the same commit.
Final checked targets must also pass an automated `admit`/`abort` scan and an
axiom-boundary review.
