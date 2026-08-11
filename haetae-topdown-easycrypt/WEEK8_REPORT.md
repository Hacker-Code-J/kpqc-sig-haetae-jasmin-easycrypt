# Week 8 report

Date: 2026-08-08

## Outcome

Week 8 is currently **CONTINUE-RANS**.

- The actual mode-2 HBZ prepare/apply layer is closed.
- The actual focused/full extraction boundary for
  `_encode_hb_z1_full` / `_decode_hb_z1_full` is closed.
- The concrete actual-array mode-2 table certificate is compiled.
- The pure quotient/slot inverse and concrete reciprocal fast-step inverse are
  compiled.
- The actual rANS core inverse and the actual success-conditioned full HBZ
  inverse remain the gating edges for `OBL-SIG-HBZ-ENCODE-DECODE`.

No Week 8 result claims `encoding delta = 0`, canonical parsing, Sign tail
reach, or implementation-level EUF-CMA security.

## Baseline

Before Week 8 edits, `scripts/verify-all.sh` passed with the Week 7 target
set. The preserved result is `logs/week8-baseline-summary.txt`.

## Closed actual leaf layer

The following authored theories fresh-compile against the Week 8 focused HBZ
extractions.

- `Mode2HbzPrepare.encode_hb_z1_prepare_core_mode2_correct`
  and `encode_hb_z1_prepare_mode2_correct`
  prove that canonical mode-2 HBZ coefficients produce `bad = 0`,
  exact symbols `signed(hbz[i]) + 6` on `[0,1024)`, and a symbol-array tail
  frame.
- `Mode2HbzApply.decode_hb_z1_apply_core_mode2_correct`
  and `decode_hb_z1_apply_mode2_correct`
  prove exact reconstruction of `[0,1024)` coefficients together with the
  coefficient-array tail frame.
- `Mode2HbzLeafRoundTrip.encode_prepare_decode_apply_mode2_inverse`
  sequentially calls the actual exported prepare and apply wrappers and proves
  the local inverse before rANS.

These results close:

- `OBL-HBZ-PREPARE-CORRECT`
- `OBL-HBZ-APPLY-CORRECT`
- `OBL-HBZ-PREPARE-APPLY-INVERSE`
- `OBL-HBZ-LEAF-FRAME`

They do not mention the rANS buffer, encoder size, or full wrapper behavior.

## Actual procedure surface

`Mode2HbzActualBoundary` proves:

- `pack_target_encode_hb_z1_full_exact_focused`
- `unpack_target_decode_hb_z1_full_exact_focused`

These theorems show that the focused Week 8 HBZ extraction and the Week 7
signature pack/unpack extraction expose the same actual full HBZ procedures.
This closes `OBL-SIG-HBZ-ACTUAL-BOUNDARY`.

## Table certificate and rANS status

### Generic certificate

`Mode2HbzTableCertificate` compiles the mode-2 arithmetic/table layer:

- 13-symbol alphabet
- positive frequencies summing to 1024
- interval partition of `[0,1024)`
- encoder esym fields
- decoder packed start/frequency words
- reciprocal-division arithmetic for the encoder-side quotient step

This is a generic certificate over the concrete mode-2 formulas used in the
theory itself.

### Concrete actual-array link

`Mode2HbzSymbolWordsGenerated` is the generated actual-array certificate. It
closes the link:

```text
actual symbol_words / dsyms_words / esyms arrays
  satisfy
mode2_hbz_table_certificate
```

This now promotes `OBL-RANS-MODE2-HBZ-TABLE-CERTIFICATE` to `PROVED`.

### rANS core

`Mode2RansCore` fresh-compiles the following mathematical results:

- `pure_rans_step_quotient`
- `pure_rans_step_slot`
- `pure_rans_step_inverse`
- `hbz_encoded_slot_selects_symbol`
- `hbz_fast_step_decode_inverse`

The last theorem combines the concrete table certificate with the pure
inverse under `0 <= s < 13` and `1 <= x < hbz_xmax(s)`.  It proves no claim
about emitted bytes or an actual generated loop.
`hbz_fast_step_preconditions_satisfiable` supplies the concrete witness
`s = 0, x = 1`.

The actual encoder prototype opened `RansEncodeTarget.M._rans_encode`, but the
nested normalization loop still lacked a backward byte-stack invariant.  The
actual suffix-copy prototype discharged its body invariant but did not finish
the quantified loop-exit projection under fresh compilation.  Both
uncompiled prototypes were removed from the authored target surface rather
than being reported as evidence.

Accordingly:

- `OBL-RANS-MODE2-HBZ-TABLE-CERTIFICATE`: `PROVED`
- `OBL-RANS-PURE-STEP-INVERSE`: `PROVED`
- `OBL-RANS-ENCODE-REFINEMENT`: `PARTIAL`
- `OBL-RANS-DECODE-REFINEMENT`: `BLOCKED`
- `OBL-RANS-SUFFIX-COPY`: `PARTIAL`
- `OBL-RANS-CORE-INVERSE`: `PARTIAL`
- `OBL-SIG-HBZ-ENCODE-DECODE`: `PARTIAL`

## Non-vacuity boundary

Week 8 preserves the required success-conditioned interpretation:

- canonical HBZ inputs alone do **not** imply successful encoding;
- any final full theorem must expose the actual encoder-success branch
  (`size <> 0`) or an equivalent disjunction;
- no theorem in this sprint assumes decoder success or round-trip equality as
  a precondition.

The local leaf witness is non-vacuous because canonical all-zero HBZ arrays
satisfy the prepare/apply premises. A successful actual full-HBZ witness is
still part of the open parent claim.

## Claim status

| Claim | Status | Boundary |
| --- | --- | --- |
| `OBL-HBZ-PREPARE-CORRECT` | `PROVED` | actual prepare leaf only |
| `OBL-HBZ-APPLY-CORRECT` | `PROVED` | actual apply leaf only |
| `OBL-HBZ-PREPARE-APPLY-INVERSE` | `PROVED` | actual prepare/apply composition only |
| `OBL-HBZ-LEAF-FRAME` | `PROVED` | local array tails only |
| `OBL-SIG-HBZ-ACTUAL-BOUNDARY` | `PROVED` | focused/full extraction identity only |
| `OBL-RANS-MODE2-HBZ-TABLE-CERTIFICATE` | `PROVED` | generic arithmetic certificate plus concrete actual-array corollary |
| `OBL-RANS-PURE-STEP-INVERSE` | `PROVED` | pure step plus concrete reciprocal arithmetic; no generated loop |
| `OBL-RANS-ENCODE-REFINEMENT` | `PARTIAL` | actual nested normalization-loop invariant missing |
| `OBL-RANS-DECODE-REFINEMENT` | `BLOCKED` | actual forward consumption/final checks not refined |
| `OBL-RANS-SUFFIX-COPY` | `PARTIAL` | no retained compiled theorem |
| `OBL-RANS-CORE-INVERSE` | `PARTIAL` | pure step closed, actual loops open |
| `OBL-SIG-HBZ-ENCODE-DECODE` | `PARTIAL` | actual leaves/table/boundary and pure step closed; actual loops/full composition/witness open |

## Verification evidence

The Week 8 verification surface performs deterministic focused extraction,
procedure-body identity checks against the Week 7 signature extraction,
deterministic regeneration of the 512-word symbol certificate, pinned
generator/output hashes, proof-hole and authored-axiom scans, fresh
`-no-eco` compilation, read-only source drift checks, selected baselines, and
the LaTeX build.  The aggregate command is:

```sh
./haetae-topdown-easycrypt/scripts/verify-all.sh
```

The final aggregate run passed:

```text
PASS baseline verification
PASS LaTeX research notes build
PASS read-only roots unchanged after verification
RESULT PASS authored-targets=38 cache=-no-eco
```

The complete summary is `logs/verify-all-summary.txt`; individual target logs
include `compile-Mode2RansCore.log` and the HBZ leaf/table/boundary logs.

## Week 9 decision

- `GO-HBZ` requires:
  concrete actual-array table certificate,
  actual rANS core inverse,
  actual success-conditioned full HBZ wrapper composition, and
  a successful actual witness.
- The concrete table and pure-step edges are closed, but the actual core is
  not.  Week 9 therefore remains `CONTINUE-RANS` and focuses only on the
  reverse normalization-byte stack / forward decoder consumption relation.
- The `h` codec does not start before `OBL-SIG-HBZ-ENCODE-DECODE` is promoted.
