# Week 16 plan — MINCORE keygen snapshot

## Decision

The active Week 16 lane is narrowed from the previous seven-calendar-day
minimum core-verification sprint to the transparent KeyGen snapshot leaf.
The `h` byte codec remains deferred.  Week 15 results remain unchanged.

The first-task exit was **CONTINUE-KG — `BLOCKED-KG-NTT-MUL`**.  The
KG-NTT-MUL continuation has now reached the time-boxed final decision
**STOP-KG-NTT**, not `GO-KG`.  The two actual helpers, their strongest sound
snapshot consequences, and the final NTT-word representation rewrite compile;
the complete `(KG-1)`--`(KG-4)` package and paper equation do not.

The subsequent Sign time box is also closed: **STOP-SIGN-CHAL-MODE2**.
The focused actual three-helper harness and its accepted-branch control
theorem compile, but the exact
`sf_challenge_mode2_highbits_lsb_sampleinball_correct` leaf does not exist in
the checked tree. Paper S-1/S-4 additionally retain the frozen full-NTT
convolution dependency. The active single lane is therefore MINCORE-VERIFY.

The paper claim is narrower than full HAETAE correctness:

> For HAETAE-2, prove the actual KeyGen matrix/finalize snapshot bridge and
> the exported mod-2q zero identity at the actual two-call boundary, then
> keep the remaining Sign, Verify, and composition lanes separate.

## Required theorem targets

### MINCORE-KG — KeyGen key equation

- Actual boundary: `ActualM23MatrixFinalizeSnapshot.run`, which calls
  `_kp_m23_matrix` and `_keypair_finalize_m23` in sequence.
- Compiled theorem surface: `actual_m23_matrix_finalize_snapshot`,
  `finalize_semantic_output_low_high_decomposition`, and
  `actual_m23_matrix_finalize_semantic_snapshot`.
- Compiled pure algebra surface:
  `Mode2KeygenSnapshotAlgebra.snapshot_low_sub_even`,
  `snapshot_residue_exact_low_high`,
  `raw_sum_raw_residue_congruent_mod_2q`, and
  `snapshot_expression_from_product_congruent_mod_2q`.
- The core theory separately proves
  `finalize_semantic_output_snapshot_mod2q_zero` and exports it through the
  actual two-call theorem.
- The compiled surface captures the KG-2-like residue split, the adjusted
  `s2 = egen-b0` component of KG-4, and a snapshot-only mod-`2q` zero
  identity.  The faithful KG-1, KG-3, complete KG-4, and paper
  `A s = q j (mod 2q)` claims are stopped on the missing odd-root
  orthogonality/full-NTT convolution theorem and the subsequent
  `Rq.poly`-to-security-list multiplication adapter.
- Do not claim sampler distribution, retry termination, or public API
  packing correctness.
- Strongest compiled theorem:
  `Mode2KeygenCoreEquation.actual_m23_matrix_finalize_semantic_snapshot`.

### MINCORE-SIGN — accepted challenge/response/hint computation

- Actual boundary: sequential calls to `_sf_round_challenge_mode2`,
  `_sf_z_check`, and `_sf_hint_mode2`.
- For a terminating accepted core execution, derive `(S-1)`--`(S-7)`:
  commitment/challenge, `z = y + (-1)^b c s`, both exact integer norm
  predicates, and the coefficientwise hint equation.
- The precondition may provide valid key and sampler representations, but it
  must not assume `reject=0`, the final equations, or output equality.
- Do not claim the sampler distribution, signing-loop termination, or a full
  1474-byte signature theorem.
- Compiled control theorem:
  `Mode2SignAcceptedCore.actual_sign_accepted_core_branch_control_mode2`.
- Stopped, unproved headline theorem:
  `Mode2SignAcceptedCore.actual_sign_accepted_core_equations_mode2`; exact
  blocker and all S-1--S-7 non-claims are recorded in
  `WEEK16_SIGN_REPORT.md`.

### MINCORE-VERIFY — reconstruction and acceptance predicate

- Actual boundary: `_verify_prepare_z1_wprime`, `_verify_matrix_crt`,
  `_sign_verify_recover_w_z2`, `_sign_verify_norm_reject`, and
  `_sign_verify_tail_m23`.
- Start after a canonical decoded `(x,v,h,c)` object has been supplied.
- Derive `(V-1)`--`(V-8)` and prove that the returned `reject=0` is equivalent
  to the exact norm-bound and recomputed-challenge conjunction.
- Do not claim full parsing or malformed-byte rejection.
- Planned headline theorem:
  `Mode2VerifyCorePredicate.actual_verify_core_predicate_mode2`.

### MINCORE-COMPOSITION — restricted completeness

- Compose the three headline results under the same generated key and the
  same prefix/context/message transcript.
- Pass the Sign result to Verify through an explicit
  `decoded_signature_object_identity` premise, not a full byte-codec claim.
- Conclude that a terminating accepted Sign core result makes the actual
  Verify core return `reject=0`.
- Planned headline theorem:
  `Mode2CoreCompleteness.accepted_sign_implies_verify_core_accept_mode2`.

## Seven-day execution order

| Day | Deliverable | Exit gate |
| --- | --- | --- |
| 1 | Freeze exact theorem signatures, extraction roots, constants and baseline | all target procedures resolve; current aggregate fresh build is recorded |
| 2 | MINCORE-KG snapshot leaf and KG-NTT audit | snapshot compiles; KeyGen freezes as `STOP-KG-NTT` |
| 3 | Sign challenge/response and norm bridges | actual procedure postconditions compose without desired-result premises |
| 4 | MINCORE-SIGN including hint | individual fresh `-no-eco` compile |
| 5 | Verify reconstruction and word/integer bridges | `(V-1)`--`(V-6)` compile against actual procedures |
| 6 | MINCORE-VERIFY and MINCORE-COMPOSITION | both individual fresh `-no-eco` compiles |
| 7 | Aggregate verification and paper freeze | fresh aggregate build, scans, manifests, ledger, audit and PDF all agree |

## Schedule guards

- Reuse compiled lower-level theorems and exact procedure-equivalence bridges;
  do not re-prove existing loop bodies.
- A headline theorem must call an actual generated procedure directly or
  through a compiled exact-equivalence bridge.
- No proof hole, authored axiom, debug declaration, assumed success result,
  assumed decoded equality, or assumed final predicate is permitted.
- If an upper caller lift threatens the deadline, freeze the theorem at the
  focused actual core boundary and disclose that boundary.  Do not replace it
  with an observation-only model or silently strengthen its assumptions.
- `PROVED` is assigned only after individual and aggregate fresh compilation.

## Explicitly deferred

- `OBL-SIG-H-ENCODE-DECODE`, metadata, padding and the full signature codec;
- canonical parsing and malformed-input rejection;
- fixed-input or general rANS termination/losslessness and all-input success;
- KeyGen and Sign termination, retry bounds and output distributions;
- public API/context-path end-to-end correctness;
- encoding delta zero, implementation security and EUF-CMA.

## Definition of done

The KeyGen task is closed as an audited partial result once the snapshot and
NTT-boundary targets individually and aggregately fresh-compile, integrity and
extraction-drift checks pass, and the ledger and paper record `STOP-KG-NTT`.
`GO-KG` was not reached.  Reopening it would first require the missing
odd-root orthogonality/full-NTT convolution theorem and the security-list
adapter; those results are not premises of the frozen theorem.

The broader Week 16 MINCORE lane is not complete. Sign is frozen as an audited
partial control result; Verify and restricted decoded-object composition are
still open.

The currently permitted KeyGen conclusion is **actual M23
matrix/finalizer snapshot functional partial correctness with KG-2
finalization semantics**.  It is not the paper KeyGen equation, full HAETAE
functional correctness, public-API correctness, termination, or
implementation security. Work proceeds with MINCORE-VERIFY.
