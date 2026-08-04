# HAETAE Jasmin–EasyCrypt Verification Plan

- **Status:** In progress — Phase 1 complete. Phase 2 includes exact-target
  mode-2 matrix arithmetic and finalization, exact machine-word semantics and
  totality for fixed-mode `_singular_full`, the constructive ideal FFT and
  extracted-root certificates, exact rounded-machine prefix/stage/schedule
  decoders, and coefficient-bounded eight-round signed safety through raw
  bound `859963392`. The immutable first-attempt trace now derives that input
  bound for all three `s1` and two finalized-`s2` slices, and the checked
  owner-stage recurrence gives each slot a coordinatewise `44833/65536`
  endpoint against `odd_dft256`. A decoded squared-magnitude and five-slice
  accumulator theorem now propagates that endpoint to ideal complex energy,
  conditional on the exact evolving signed-safe `W32` trace. Discharging that
  trace, retry-attempt lifting, tie-policy decision, acceptance and retry
  termination, packing semantics, and the NTT/matrix-to-security-model
  multiplication bridge remain open.
- **Created:** 2026-07-13
- **Project root:** `haetae-ref-easycrypt/`
- **Implementation under verification:** `../haetae-ref-jasmin/`
- **Default specification baseline:** `../haetae-security/HAETAE_v260204.pdf`

## 1. Objective

Build a reproducible EasyCrypt verification workspace that connects the
provable-security argument in the HAETAE specification to the actual Jasmin
source in `haetae-ref-jasmin`.

The final result must establish two separate facts and then compose them:

1. **Algorithm security:** the paper-faithful HAETAE model satisfies the stated
   EUF-CMA bound in the random-oracle model under the declared MLWE and
   Module-SIS assumptions.
2. **Implementation correctness:** the public Jasmin key-generation, signing,
   and verification procedures refine that paper-faithful model for modes 2,
   3, and 5.

Only after both facts are machine-checked may the project state a source-level
security result for the Jasmin implementation. Any claim about generated
assembly must name Jasmin compiler semantic preservation as part of the trusted
computing base. Memory safety, constant-time behavior, speculative
constant-time behavior, and physical side-channel resistance remain distinct
claims.

## Progress

- **P0 complete:** specification/source hashes, toolchain record, assumption
  register, claim boundaries, traceability seed, and baseline scripts exist.
- **P1 complete:** forced Jasmin build/KAT, fresh managed-security compilation,
  the existing NTT proof bundle, 140-declaration inventory, and 104-premise
  inventory all pass deterministic checks.
- **P2 in progress:** seven generated extraction surfaces now have deterministic
  drift checks: NTT, FIPS202/SHAKE, seed XOF, uniform XOF, eta XOF, sampler
  callers, and the actual mode-2 key-generation parent. The parent closure
  covers 32 files and 56 procedures. The dedicated parent proof gate checks
  pinned inputs, both relevant extraction closures, 24 byte-identical shared
  theories, and 17 generated/authored proof artifacts with `-no-eco`.
- **Sampler-prefix milestone:** seven relational bridges transport the seed,
  leaf, and caller contracts to `KeygenMode2ParentTarget.M`. A proof-only
  observer then follows the actual parent call order through exact seed
  expansion, six matrix sampler calls, two vector sampler calls, and five
  first-attempt eta calls. Its Hoare theorem gives exact finite-stream,
  range/centered-range, frame, slice, and counter semantics. Its pHoare theorem
  gives probability-one termination under 13 explicit deterministic
  finite-progress certificates. The gate passes 17/17 fresh compilations with
  no proof holes or authored axioms.
- **Target NTT milestone:** compiled relational bridges identify the current
  target's Montgomery helper and direct-loop single-polynomial NTT procedures
  with the checked loop adapter. Six polynomial Hoare theorems establish the
  algebraic forward and inverse postconditions for both the internal
  procedures and public wrappers, including inverse input bounds 16 and 18.
  The dedicated gate pins all 18 imported support theories, checks three shared
  generated representations byte-for-byte, and compiles the authored target
  proof with no holes or new axioms.
- **Mode-2 matrix-arithmetic and finalization milestone:** the actual extracted
  `_kp_m23_matrix` has a fixed `(rows, cols) = (2, 3)` algebraic and totality
  proof. Checked wide-slice adapters lift the single-polynomial forward theorem
  across three `BArray8192` slices, the actual pointwise loop computes two rows
  of exactly three Montgomery-reduced products at bound 18, and the extended
  inverse theorem returns both rows at bound 16. The direct Hoare theorem
  `kp_m23_matrix_mode2_arithmetic_correct` composes those stages with the exact
  768-word copy and 512/768-word tail frames.
  `kp_m23_matrix_mode2_ll` separately proves probability-one termination of
  the complete actual helper; the previous scratch-independence results remain
  checked. `CheckedMode2ParentM23Prefix.run` composes this helper after the
  checked sampler prefix and exports semantic and certificate-conditioned
  progress theorems.
  `KeygenM23FinalizeSpec` records the exact extracted freeze, frozen-sum, and
  word-level EGen low/high operations. `keypair_finalize_m23_mode2_correct`
  proves both exact first-512-word finalizer results and both tail frames for
  the actual `_keypair_finalize_m23`; `freeze_word_ll`,
  `keypair_finalize_m23_ll`, and `keypair_finalize_m23_mode2_ll` establish
  scalar, unconditional-helper, and fixed-mode totality. The proof-only
  `CheckedMode2ParentM23Finalize.run` preserves the sampler and M23 facts and
  adds the exact finalizer output, with certificate-conditioned probability-one
  termination. `KeygenM23FinalizeSemantics` proves that the scalar freeze is
  canonical reduction modulo `q = 64513` under its signed-18-bit premise.
  `KeygenM23FinalizeArraySemantics` derives that premise across all 512 active
  words from the M23 bound-16 result, centered `s2`, and canonical uniform
  coefficients, and gives the exact adjusted-`s2` equation plus both tail
  frames. `KeygenM23FinalizeHAETAEBridge` identifies the local low/high
  operations pointwise with `HAETAE_Algebra` coefficient decomposition. The
  new `TargetKeygenM23FullFirstAttempt` theorem peels the mandatory first
  iteration of the actual fixed-mode `_keypair_full_m23` into a result-carried
  mirror, proves equality of the final packed key arrays, and leaves the
  residual retry loop and both packing calls operationally unchanged. The
  mirror's immutable trace carries the exact sampler, M23, word-finalizer,
  canonical, and HAETAE pointwise facts, the first counter value `5`, the
  exact fixed-mode `_singular_full` word evaluator, protected bound `611098`,
  and the exact unsigned guard relation. The singular proof follows all five
  threaded scratch-state FFT invocations, all eight stages of each FFT, the
  accumulated machine squared magnitudes, and the five-entry finish logic; a
  separate theorem proves probability-one termination for the fixed
  `(3, 2, 5, 58, 24)` call. The trace guard is equivalent to
  `W64.to_uint(score) <= 611098`. `KeygenM23FixedPointSemantics` proves the
  exact local Q16 decoder and rounding interval under a signed-fit premise;
  `KeygenM23SingularBoundary` records the remaining range obligations and
  proves that five selected zeros score `120` under the implementation's
  tied-minimum rule versus `256` under the paper's fixed weights;
  `KeygenM23SingularZeroFinish` carries the zero invariant through the actual
  selector and finish pipeline and obtains the same implementation score.
  `KeygenM23SingularIntegerSemantics` decodes the local initialization,
  scalar butterfly, squared-magnitude, and accumulator kernels under those
  explicit range premises. `KeygenM23ComplexReal` provides transparent
  real-pair complex algebra, norm, and coordinate-error laws without a
  project-authored axiom. `KeygenM23IdealRootDFT` uses proved standard square
  roots to construct the lower-half-plane 512th root, checks its dyadic
  primitivity criterion and power anchors, defines the abstract 256-point
  odd-root DFT, and proves the coefficient-twist identity.
  `KeygenM23IdealFFTSchedule` proves that the pure exact-complex bit-reversed
  eight-stage schedule computes `dft256` and that its twisted input computes
  `odd_dft256`. `KeygenM23RootGeneratorCertificate`,
  `KeygenM23RootTableRounding`, and `KeygenM23RootTableTargetBridge` prove
  that all 256 extracted root pairs are the unique nearest Q16 encodings of
  the corresponding `ideal_root` coordinates, with strict coordinate error
  below `1/131072`. `KeygenM23SingularFFTInitBridge` then decodes all 256
  complex-cell updates (512 word stores) in the initialization fold, proves
  every raw initialization product signed-safe under coefficient magnitude at
  most two, frames all other bit-reversed cells at each step, and gives
  whole-vector error at most `1/65536` against the exact bit-reversed twisted
  input. `KeygenM23SingularFFTButterflyBridge` now gives one valid,
  distinct-index butterfly exact four-word writes, exact decoded even/odd
  destinations under `fft_butterfly_safe_at`, a frame for every other cell,
  and `1/65536` coordinatewise local rounding error against the exact complex
  butterfly over decoded operands. `KeygenM23SingularFFTKPrefixBridge` lifts
  the exact decoded destination and frame facts through any valid inner
  `fft_k_prefix`, using a rounded observer whose processed cells are evaluated
  on their exact evolving pre-step states.
  `KeygenM23SingularFFTBlockPrefixBridge` composes every complete inner loop
  through an arbitrary valid block prefix using the exact evolving pre-block
  state and an explicit per-block safety contract. `KeygenM23SingularFFTStageBridge`
  now closes the exact one-stage lift below this theorem, and
  `KeygenM23SingularFFTScheduleBridge` composes those stage endpoints across
  the eight executing rounds on the decoded machine surface. The raw-word
  bound theories now discharge coefficient-bounded schedule safety and prove
  final signed storage. `TargetKeygenM23SingularFFTInputBounds` derives the
  coefficient premise for the three sampled `s1` and two finalized-`s2`
  slices in the immutable first-attempt trace, so every valid first-attempt
  slot has schedule safety, the final `859963392` raw bound, and the
  coordinatewise `44833/65536` error endpoint against the exact ideal schedule
  for arbitrary scratch input. `KeygenM23SingularFFTAccumulatorBridge` proves
  the local `1/65536` squared-magnitude decode error and folds the resulting
  ideal-energy error through all five accumulator updates;
  `TargetKeygenM23FirstAttemptAccumulator` discharges the input premise while
  retaining the evolving accumulator-safety trace. Retry-attempt lifting and
  discharge of that trace remain open.
  `KeygenM23FFTTableCertificate` proves that the
  extracted `jfft_brv8` table is exactly `bsrev 8` and that all signed root
  coordinates lie in `[-65536,65536]`. `KeygenM23SingularTieRegression`
  proves an already-selected equal-value finish case with scores `375000` and
  `800000` on opposite sides of the `611098` guard; it does not prove FFT
  reachability. The current multiplicity-sensitive implementation rule is
  preserved because, if such a tie is reachable, changing its rejection
  decision may change a retry-selected key pair.
  This is
  partial correctness: it neither
  proves that the first attempt accepts nor establishes outer-loop
  termination, retry-attempt coefficient-bound/error propagation, or
  the signed-safe accumulator trace needed to make the conditional energy
  theorem unconditional, a
  versioned tie-policy change, or packing correctness.
  The gate
  checks source and
  support hashes, extraction drift, fresh `-no-eco`
  compilation of the current manifest, and hole/axiom/debug scans.
- **P3 remains open:** strengthen the fixed-mode packed-output/first-attempt
  result into a complete semantic refinement. The next path includes the
  NTT/matrix-to-list bridge for the security model's polynomial multiplication,
  a discharge or quantified bad-event account for the signed `W32`
  squared-magnitude and accumulator trace, an explicit versioned
  tie-policy decision, proof of
  acceptance and outer-retry termination,
  packing semantics, and pointer aliasing, separation, representation, and
  safety. Universal certificate existence, rejection distributions,
  public-API key generation, modes 3 and 5, signing, verification, and
  composition with the security theorem also remain open.

## 2. Requirements Summary

- Use EasyCrypt for specifications, probabilistic games, reductions, and
  implementation-refinement proofs.
- Generate EasyCrypt procedure models from the actual files under
  `haetae-ref-jasmin/jasmin/`; do not silently substitute the separate
  `haetae-ntt-verify/jasmin/hpoly.jazz` source.
- Cover the public `crypto_sign_keypair`, `crypto_sign`, and
  `crypto_sign_verify` behavior described in
  `haetae-ref-jasmin/README.md:8-13` and `haetae-ref-jasmin/README.md:264-277`.
- Cover HAETAE modes 2, 3, and 5, using mode 2 as the first end-to-end vertical
  slice and parameterized lemmas where the program structure is shared.
- Reuse existing checked artifacts when their source and assumptions match;
  otherwise reuse only their proof method.
- Preserve a traceability chain from specification statement, through
  EasyCrypt lemma, through extracted Jasmin procedure, to verification command
  and log.
- Compile checked targets from source with `-no-eco`, reject proof holes, and
  inventory every axiom and unproved premise.
- Provide step-by-step documentation sufficient for a new contributor to
  reproduce each proof result.

## 3. Current Evidence and Starting Boundaries

### 3.1 Jasmin implementation

- The production scheme is implemented in Jasmin; C is retained for test, KAT,
  and benchmark harnesses (`haetae-ref-jasmin/README.md:3-6`).
- Key generation, signing, and verification are routed through Jasmin for all
  three modes (`haetae-ref-jasmin/docs/full-jasmin-port.md:98-149`).
- The existing behavioral gate runs sign/verify smoke tests and byte-for-byte
  KAT comparisons (`haetae-ref-jasmin/README.md:279-310`).
- The concrete internal entry points begin at:
  - key generation: `haetae-ref-jasmin/jasmin/keypair.jazz:1305`
  - signing: `haetae-ref-jasmin/jasmin/sign.jazz:2725`
  - verification: `haetae-ref-jasmin/jasmin/verify.jazz:445`

### 3.2 Existing security proof surface

- `haetae-security/provable-security/` already separates the managed
  provable-security files from implementation-validation artifacts
  (`haetae-security/provable-security/README.md:1-8`).
- Its manifest covers the top theorem, ROM interface, hop games, reductions,
  scheme, transcript, events, assumptions, distributions, rejection sampling,
  algebra, parameters, and FIPS202/Keccak support
  (`haetae-security/provable-security/proof-files.txt:4-28`).
- The current recorded run reports all 16 manifest entries passing and ends in
  `RESULT: PASS`
  (`haetae-security/provable-security/logs/last-run-summary.txt:9-41`).
- Passing compilation is not yet a final paper-faithful proof. The repository's
  gap table explicitly records remaining high-risk work in the Module-SIS
  handoff, public-key/Jasmin algebra, real signing equations, challenge
  distribution, rejection sampling, forking extraction, and top-level theorem
  (`haetae-security/PAPER_CORRESPONDENCE_GAPS.md:7-16`).

### 3.3 Existing Jasmin-to-EasyCrypt method

- `haetae-ntt-verify/easycrypt-ct/` already demonstrates reproducible
  `jasmin2ec` extraction, pRHL refinement, and end-to-end NTT wrapper theorems
  (`haetae-ntt-verify/easycrypt-ct/README.md:13-32`).
- Its verification compiles in dependency order with `-no-eco`, scans for
  `admit`/`abort`, and confines axioms to declared foundational boundaries
  (`haetae-ntt-verify/easycrypt-ct/README.md:64-79`).
- The extraction command and generated-array model are documented in
  `haetae-ntt-verify/easycrypt-ct/scripts/regenerate-extract.sh:26-33`.
- The NTT proof source and `haetae-ref-jasmin/jasmin/hpoly.jazz` currently have
  a large source diff. The current target is nevertheless now covered at the
  single-polynomial boundary by `TargetNTTRefinement`: its extracted
  direct-loop procedures are related explicitly to the checked loop adapter,
  rather than treating the two Jasmin sources as identical. The fixed mode-2
  parent lifting through three forward slices, the pointwise accumulator, and
  two bound-18 inverse slices is now checked by the M23 arithmetic gate. Other
  modes and wide-array consumers remain separate obligations.

## 4. Claim Ladder

Each row is a separate deliverable. A lower row must not be used as evidence
for a higher row until the intervening proof is complete.

| Level | Claim | Required evidence |
| --- | --- | --- |
| L0 | The implementation builds and matches known answers | `make test`, KAT diffs, archived tool versions |
| L1 | EasyCrypt models were generated from the target Jasmin source | deterministic `jasmin2ec` regeneration and zero extraction drift |
| L2 | Extracted primitives refine mathematical operations | pRHL/Hoare lemmas for representations, arithmetic, NTT, SHAKE, packing, and samplers |
| L3 | Extracted public APIs refine HAETAE keygen/sign/verify | mode-specific end-to-end equivalence theorems with explicit randomness and memory preconditions |
| L4 | The paper-faithful HAETAE model satisfies the stated security bound | checked game hops and reductions with only classified cryptographic assumptions |
| L5 | The Jasmin source inherits the model's security bound | a checked composition theorem from L3 and L4 plus an explicit trusted-computing-base statement |

## 5. Proposed Project Layout

The following structure will be created incrementally; generated files and logs
must be clearly distinguished from authored proof sources.

```text
haetae-ref-easycrypt/
├── README.md
├── PLAN.md
├── easycrypt/
│   ├── spec/          # Paper-faithful deterministic and probabilistic model
│   ├── extract/       # jasmin2ec output from haetae-ref-jasmin only
│   ├── refinement/    # Representation and functional-correctness lemmas
│   ├── security/      # Games, reductions, adapters, composition theorem
│   └── support/       # Shared arrays, words, algebra, and bounded distributions
├── manifests/
│   ├── sources.sha256
│   ├── proof-files.txt
│   ├── assumptions.md
│   └── traceability.csv
├── scripts/
│   ├── regenerate-extract.sh
│   ├── check-extract-drift.sh
│   ├── verify-functional.sh
│   ├── verify-security.sh
│   └── verify-all.sh
├── docs/
│   ├── 00-scope-and-claims.md
│   ├── 01-toolchain-and-reproduction.md
│   ├── 02-specification-correspondence.md
│   ├── 03-representation-relations.md
│   ├── 04-keygen-refinement.md
│   ├── 05-sign-refinement.md
│   ├── 06-verify-refinement.md
│   ├── 07-security-reductions.md
│   ├── 08-composition-and-trust.md
│   └── proof-status.md
└── logs/              # Reproducible run evidence; retention policy documented
```

## 6. Implementation Plan

### Phase 0 — Establish the verification contract

1. Create the project README, directory layout, manifests, and verification
   script stubs.
2. Pin the selected HAETAE specification by filename and SHA-256. Treat
   `HAETAE_v260204.pdf` as the initial baseline; record any theorem or parameter
   difference from `HAETAE_TCHES2024.pdf` rather than blending versions.
3. Record EasyCrypt, Jasmin, `jasmin2ec`, Why3, SMT prover, compiler, and OS
   versions.
4. Hash all target `.jazz` and `.jinc` inputs and the KAT response files.
5. Define the permitted proof boundary: imported mathematical axioms,
   cryptographic hardness assumptions, ROM assumptions, compiler semantics,
   and system RNG contract.
6. Start `manifests/traceability.csv` with one row for every specification
   algorithm step and theorem term.

**Gate P0:** A clean checkout can identify the exact specification, source,
toolchain, assumptions, and commands that future claims refer to.

### Phase 1 — Reproduce and classify the existing baselines

1. Run `make -C haetae-ref-jasmin test`; archive the mode-2/3/5 smoke-test and
   KAT results.
2. Run the existing provable-security verifier using the command documented at
   `haetae-security/provable-security/README.md:42-61`.
3. Run the existing NTT functional-correctness verifier documented at
   `haetae-ntt-verify/easycrypt-ct/README.md:50-62`.
4. Scan the checked security sources for `admit`, `abort`, axioms, abstract
   operators, and theorem premises. Classify each occurrence as foundational,
   cryptographic, implementation-related, or an open obligation.
5. Convert every row of `haetae-security/PAPER_CORRESPONDENCE_GAPS.md` into a
   blocking issue in `docs/proof-status.md`; compilation alone may not close
   these issues.

**Gate P1:** Baseline commands pass from a fresh state, and every assumption or
placeholder has an owner, rationale, and closure criterion.

### Phase 2 — Extract the actual Jasmin verification surface

1. Determine the smallest compilable extraction units for the target public
   paths. Start with leaf components and proceed to `keypair.jazz`,
   `sign.jazz`, and `verify.jazz` because monolithic extraction will create
   unnecessarily large proof states.
2. Generate EasyCrypt files with `jasmin2ec --array-model=barray`, adapting the
   proven regeneration pattern from
   `haetae-ntt-verify/easycrypt-ct/scripts/regenerate-extract.sh:26-33`.
3. Store generated modules under `easycrypt/extract/`; never hand-edit them.
4. Generate shared array theories into the same controlled extraction surface.
5. Add a drift check that regenerates into a temporary directory and fails if
   tracked extraction output differs.
6. Map each extracted procedure to its `.jazz` source and public/internal API
   role in `manifests/traceability.csv`.

**Gate P2:** Extraction is deterministic, originates only from the hashed
`haetae-ref-jasmin` sources, and all generated modules compile with `-no-eco`.

### Phase 3 — Prove representations and arithmetic primitives

1. Define representation relations for bytes, `W32`/`W64`, signed
   coefficients, Montgomery values, polynomials, vectors, matrices, packed
   buffers, pointer slices, and descriptor arguments.
2. State range, length, separation, and aliasing preconditions explicitly.
3. Prove word-level reduction, addition/subtraction, Montgomery
   multiplication, decomposition, norm, and fixed-point helper contracts.
4. Port the existing NTT proof method to the extraction generated from
   `haetae-ref-jasmin/jasmin/hpoly.jazz`. Reuse a theorem only if source identity
   or a checked equivalence to the old NTT source has been established.
5. Compose polynomial lemmas into vector and matrix operations used by keygen,
   sign, and verify.
6. Instantiate shared proofs for modes 2, 3, and 5 and prove every parameter
   side condition.

**Gate P3:** Every arithmetic primitive reachable from the public APIs has a
compiled functional contract and no unclassified representation assumption.

### Phase 4 — Prove hashes, encodings, and sampling interfaces

1. Connect the extracted Keccak/SHAKE byte and memory behavior to the
   paper-level random-oracle domains, including padding, domain separation,
   absorb order, squeeze lengths, and little-endian lane encoding.
2. Close the FIPS202/Jasmin memory-equivalence work identified at
   `haetae-security/PAPER_CORRESPONDENCE_GAPS.md:9-13` and
   `haetae-security/PAPER_CORRESPONDENCE_GAPS.md:47-54`.
3. Prove pack/unpack round trips, canonical encodings, rejection behavior,
   signature length checks, and zero-padding checks.
4. Refine uniform, eta, Gaussian, hyperball, branch-bit, and challenge samplers
   to explicit EasyCrypt distributions. Prove support, losslessness or the
   stated termination condition, point probabilities, and independence/freshness.
5. Relate concrete SHAKE streams and rejection loops to the probabilistic
   sampler interfaces used by the security games.

**Gate P4:** Byte transcripts and sampler distributions used by the extracted
implementation are the same objects consumed by the security model, or a
checked statistical-distance bound is stated and propagated.

### Phase 5 — Prove public API functional correctness

Proceed vertically, completing mode 2 before generalizing to modes 3 and 5.

1. **Key generation:** prove seed expansion, matrix/secret sampling, NTT
   arithmetic, rejection conditions, singular-value checks, and key packing.
2. **Verification:** prove signature/public-key decoding, matrix arithmetic,
   norm and format rejection, transcript reconstruction, challenge
   recomputation, and the public return code.
3. **Signing:** prove secret-key decoding, message transcript, hyperball
   sampling, challenge construction, response/hint construction, both rejection
   checks, packing retry, and randomized wrapper behavior.
4. Prove API-level memory framing: output lengths, unchanged out-of-frame
   memory, permitted aliasing, and failure-path behavior.
5. State and compile mode-specific end-to-end theorems relating each extracted
   public procedure to the paper-faithful `KeyGen`, `Sign`, and `Verify` model.
6. Cross-check deterministic instances against the existing mode-2/3/5 KATs;
   keep KAT evidence labeled as testing rather than proof.

**Gate P5:** Nine end-to-end refinement results compile: keygen, sign, and
verify for each of modes 2, 3, and 5.

### Phase 6 — Close the paper-security correspondence gaps

1. Replace the structural public-key model with the exact HAETAE matrix,
   sampling, NTT placement, rounding, rejection, and packing equations.
2. Replace the structural signing model with the exact hyperball sample,
   commitment, full transcript challenge, response, hint, rejection, and
   accepted-output distribution.
3. Prove challenge support/cardinality, point-probability, and min-entropy facts
   for the actual encoded transcript.
4. Prove the real-to-simulated signing and rejection-sampling hops with explicit
   loss terms.
5. Complete ROM programming/freshness arguments for the concrete domain
   encodings.
6. Complete the two-transcript forking extractor and derive the paper's
   bimodal/self-target Module-SIS relation with the exact norm bound.
7. Define exact MLWE and Module-SIS games and connect reduction outputs to
   their instance distributions.
8. Refactor the top-level EUF-CMA theorem until it assumes only the documented
   hardness, ROM, and concrete parameter/query premises—not structural
   stand-ins for implementation behavior.

**Gate P6:** Every blocking row in `PAPER_CORRESPONDENCE_GAPS.md` is discharged
by a named compiled lemma or retained as an explicitly documented blocker; a
final security claim is forbidden while any high-risk row remains open.

### Phase 7 — Compose implementation correctness with provable security

1. Define adversary adapters between the extracted Jasmin API experiment and
   the paper-level EUF-CMA experiment.
2. Use the Phase 5 equivalences to replace Jasmin keygen/sign/verify calls with
   the paper-faithful procedures.
3. Apply the Phase 6 security theorem and propagate all probability and
   statistical-distance terms without informal rewriting.
4. State the final source-level theorem separately for modes 2, 3, and 5.
5. Publish a trust statement covering EasyCrypt, Why3/provers, Jasmin
   extraction/compiler semantics, the system RNG, and any remaining axioms.
6. State exactly what does not follow: physical side-channel resistance,
   fault resistance, platform RNG quality, and claims about modified or
   unpinned sources.

**Gate P7:** A fresh proof run compiles a named implementation-security theorem
for each mode, and the theorem statement contains every retained assumption and
loss term.

### Phase 8 — Automate verification and publish step-by-step documentation

1. Implement `scripts/verify-all.sh` to run source hashing, extraction drift,
   fresh EasyCrypt compilation, proof-hole scanning, axiom-boundary scanning,
   Jasmin tests, and summary generation in dependency order.
2. Ensure a failed prerequisite stops downstream claim generation.
3. Write one document per proof boundary using the structure: purpose,
   definitions, source mapping, theorem statement, proof strategy, command,
   expected result, assumptions, and remaining limitations.
4. Maintain `docs/proof-status.md` as the authoritative claim matrix with
   `NOT STARTED`, `IN PROGRESS`, `BLOCKED`, or `VERIFIED` status and links to
   exact lemmas/logs.
5. Add a clean-room reproduction guide and test it from a clean checkout.
6. Generate a concise final report from machine-readable manifests rather than
   manually copying proof status.

**Gate P8:** A new contributor can reproduce all reported results using the
documented commands, and the generated report agrees with the proof manifest.

## 7. Acceptance Criteria

The project is complete only when all of the following are true:

- [ ] The selected specification, every Jasmin input, all KAT baselines, and
      the proof toolchain are versioned or cryptographically fingerprinted.
- [ ] Extraction regeneration from `haetae-ref-jasmin` produces zero diff.
- [ ] All proof-manifest entries compile from source with `easycrypt compile
      -no-eco`.
- [ ] Checked targets contain no `admit` or `abort` proof holes.
- [ ] Every `axiom`, abstract operator, oracle idealization, hardness
      assumption, and theorem premise appears in `manifests/assumptions.md`.
- [x] The actual Jasmin NTT source—not only the separate NTT-project source—is
      connected to the mathematical NTT theorem.
- [x] The actual fixed-mode `_kp_m23_matrix` composes wide-array NTT and exact
      three-column pointwise arithmetic and has a probability-one termination
      theorem.
- [x] The actual mode-2 `_keypair_finalize_m23` has exact 512-word
      input-relative outputs, both tail frames, and helper/fixed-mode totality
      theorems. Its scalar freeze is canonical modulo `64513` under the
      signed-18-bit premise, and the reachable 512-word observer derives that
      premise and returns the pointwise `HAETAE_Algebra` high decomposition and
      exact low-adjusted `s2`.
- [ ] Keccak/SHAKE memory behavior and all HAETAE transcript encodings are
      connected to the ROM domains used by the security proof.
- [ ] Keygen, sign, and verify refinement theorems compile for modes 2, 3, and
      5 with explicit memory and randomness contracts.
- [ ] Every high-risk paper-correspondence gap has a compiled closing lemma.
- [ ] The final EUF-CMA theorem exposes only classified cryptographic and trust
      assumptions and contains the complete loss bound.
- [ ] The implementation-security composition theorem compiles for each mode.
- [ ] `make -C haetae-ref-jasmin test` passes for all modes.
- [ ] A single documented command produces a passing, timestamped verification
      summary from a clean checkout.
- [ ] Documentation distinguishes tests, source extraction, functional
      correctness, cryptographic security, compiler trust, constant-time
      checks, and excluded physical leakage claims.

## 8. Verification Strategy

The eventual top-level verification flow is:

```sh
make -C haetae-ref-jasmin test
cd haetae-security && sh provable-security/verify-provable-security.sh
cd ../haetae-ntt-verify/easycrypt-ct && \
  ./scripts/check-full-functional-correctness.sh
cd ../../haetae-ref-easycrypt && ./scripts/verify-all.sh
```

`verify-all.sh` must add these project-specific gates:

1. source and specification fingerprint validation;
2. deterministic `jasmin2ec` extraction and drift comparison;
3. fresh dependency-ordered EasyCrypt compilation;
4. proof-hole and unexpected-axiom scans;
5. separate functional-correctness and security summaries;
6. traceability completeness checks;
7. final composition theorem compilation.

## 9. Risks and Mitigations

| Risk | Impact | Mitigation |
| --- | --- | --- |
| Existing security files compile but model structural stand-ins | A false “fully proved” claim | Treat every gap-table row as blocking and require named closing lemmas |
| Existing NTT proof targets a materially different `hpoly.jazz` | Invalid transfer of correctness | Regenerate from the target source and prove equivalence or redo refinement |
| Full Jasmin extraction is too large or unsupported | Proof development stalls | Extract leaf modules, verify stable interfaces, then compose public paths |
| Rejection loops obscure termination and output distributions | Invalid signing-security hop | Prove losslessness/termination and accepted distribution before composition |
| Concrete SHAKE bytes do not match ROM domain encodings | Security games describe another scheme | Prove padding, domain separation, absorb order, lengths, and memory equivalence |
| Signed/Montgomery/range representations are conflated | Arithmetic proof unsoundness | Centralize representation relations and require range lemmas at every boundary |
| Parameter-mode duplication creates divergent proofs | Mode-specific gaps | Prove shared parametric lemmas, then discharge explicit mode side conditions |
| Generated `.ec` files are edited manually | Extraction evidence becomes unverifiable | Make extraction generated-only and enforce regeneration drift checks |
| Proof succeeds through stale `.eco` files | False reproducibility | Compile with `-no-eco` and preserve per-target logs |
| Jasmin source changes after proof completion | The claim no longer covers the code | Hash inputs and fail verification on unreviewed source drift |
| “Implementation security” is read as physical security | Claim overreach | Publish a layered claim matrix and explicit exclusions |

## 10. Documentation and Commit Sequence

Keep each commit limited to one proof boundary. Suggested sequence:

```text
[260713] add: scaffold HAETAE EasyCrypt verification workspace
[260713] docs: define HAETAE verification claims and trust boundary
[260713] build: add reproducible Jasmin-to-EasyCrypt extraction
[260713] prove: establish shared representation and arithmetic contracts
[260713] prove: connect HAETAE NTT and SHAKE primitives
[260713] prove: refine HAETAE key generation for all modes
[260713] prove: refine HAETAE verification for all modes
[260713] prove: refine HAETAE signing and rejection loops
[260713] prove: close HAETAE security game correspondence gaps
[260713] prove: compose Jasmin correctness with EUF-CMA security
[260713] docs: publish reproducible HAETAE proof walkthrough
```

Each proof commit should state the theorem or gap it closes, list retained
assumptions, and record the exact verification command in the commit body.

## 11. Definition of Done

“Done” means more than successful EasyCrypt compilation. It means that a named,
paper-faithful EUF-CMA theorem and named public-API refinement theorems are
machine-checked for the exact pinned Jasmin sources, a final theorem composes
those layers, every assumption is visible, every remaining limitation is
honestly scoped, and an independent clean run reproduces the evidence.
