# Frozen paper artifact manifest

This is the canonical artifact manifest for the frozen paper scope.  The
verdict `PAPER-FROZEN` means that the document, proof inventory, generated
artifacts, and reproducibility checks agree on the boundary below.  It does
not mean that HAETAE KeyGen, Sign, Verify, or EUF-CMA security is proved end to
end.

## Frozen result matrix

| Lane | PROVED slices | PARTIAL parent | BLOCKED claims |
| --- | --- | --- | --- |
| `PAPER-KG` | actual-procedure first-attempt, prefix/export, matrix-to-finalizer snapshot, KG-2 coefficient split, adjusted `e-b0` component | terminating-run and snapshot-level KeyGen refinement | KG-1, KG-3, complete KG-4, `A s = q j (mod 2q)`, retry termination and distribution |
| `PAPER-SIGN` | actual raw-mu helpers and frames, actual accepted-core branch control, signature-prefix plus HBZ/rANS codec vertical slice | Hoare partial correctness and success-conditioned codec results | paper S-1--S-7, full signing correctness, termination and accepted-output distribution |
| `PAPER-VERIFY` | actual five-helper order, word-level V-1/V-2/V-5/V-6 reconstruction projections, W64 norm decision, tail trace and mismatch word | machine-word reconstruction/norm boundary | paper V-3/V-4, matrix/CRT polynomial semantics, challenge semantics and full Verify correctness |
| `PAPER-SIGN-VERIFY` | actual sequential trace/control and local generated mu adapters | accepted-path memory and stored-observation bridge | legitimate Sign output accepted by Verify and the full Sign-to-Verify composition |

Every `PROVED` entry means only that its named theorem fresh-compiles with its
displayed premises.  In particular, the table does not promote a proved leaf
to its partial or blocked parent.

## Primary checked artifacts

- `manifests/proof-targets.txt`: the complete set of 82 authored EasyCrypt
  targets.
- `easycrypt/refinement/keygen/`: actual first-attempt, packed-key, matrix
  snapshot, finalization, and stopped NTT-boundary results.
- `easycrypt/refinement/sign/`: actual signature-prefix and HBZ/rANS codec
  vertical slice plus the stopped accepted-core control boundary.
- `easycrypt/refinement/verify/`: the four actual-procedure Verify targets for
  call order, reconstruction words, norm decision, and tail trace.
- `easycrypt/refinement/composition/`: raw actual-procedure transcript,
  address, memory, frame, and accepted-path adapters.
- `manifests/generated-extractions.sha256` and
  `manifests/generated-certificates.sha256`: deterministic generated-artifact
  drift checks.
- `manifests/sources.sha256` and `manifests/source-roots.md`: pinned input and
  read-only-root inventory.
- `CLAIM_LEDGER.md` and `THEOREM_GRAPH.md`: statement-level status and
  dependency boundary.
- `WEEK16_KG_NTT_MUL_REPORT.md`, `WEEK16_SIGN_REPORT.md`, and
  `WEEK16_VERIFY_REPORT.md`: exact stop records.
- `latex/main.pdf`: the frozen paper PDF built from `latex/main.tex`.
- `logs/verify-all-summary.txt`: the tracked aggregate summary.  Detailed
  compile logs are reproducible local artifacts under the ignored `logs/`
  tree.

No new EasyCrypt theorem belongs to the paper-freeze change.  The authored
proof manifest therefore remains exactly 82 targets.

## Exact semantic blockers

### KeyGen

The checked actual matrix output stops at a full-inverse-NTT expression.  Its
first missing semantic identity is the Montgomery spectral action

```text
array256_mont(full_invntt(ahat * full_ntt(p) * inv R))
= full_invntt(ahat) Rq.&* p.
```

It needs the absent 256-term odd-root orthogonality theorem.  A subsequent
`Rq.poly`-to-`HAETAE_Algebra.poly_mul` list adapter is also absent.  Therefore
the snapshot congruence is not the paper equation `A s = q j (mod 2q)`.

### Sign

The first Sign-specific missing leaf is
`sf_challenge_mode2_highbits_lsb_sampleinball_correct`.  Paper S-1 and S-4
also depend on the stopped full-NTT convolution bridge; S-4 needs a response
representation theorem; S-5/S-6 need signed-word and W64 no-wrap semantics;
and S-7 needs `_sf_hint_mode2_hint_equation_correct`.  S-1--S-7 are not
claimed.

### Verify

The stopped combined leaf
`verify_matrix_crt_mode2_fromcrt_freeze_exact` has two procedural children:

```text
verify_matrix_ntt_acc_mode2_cols4_correct
├── rq_mul_coeff_foldr_to_bigi
├── full_ntt_montgomery_spectral_action
└── odd-root orthogonality (256 terms)

verify_crt_freeze_mode2_word_exact
```

The separate challenge leaf
`verify_tail_m23_highbits_lsb_sampleinball_correct` is also absent.  Hence
V-3/V-4 and the full Verify predicate are not claimed.

### End-to-end composition

`OBL-DIRECT-OBSERVED-MU`, legitimate Sign-output tail reach, the complete
codec/parser boundary, all paper Sign/Verify equations, termination, and
distribution results remain open.  No full Sign-to-Verify theorem is claimed.

## Reproduction and expected result

From the repository root, run:

```sh
./haetae-topdown-easycrypt/scripts/verify-all.sh
./haetae-topdown-easycrypt/scripts/check-paper-freeze.sh
```

The aggregate must contain exactly 82 lines beginning `PASS fresh compile`
and exactly one terminal line:

```text
RESULT PASS authored-targets=82 cache=-no-eco
```

The verifier regenerates focused extractions and certificates, checks their
hashes, scans holes/axioms/debug declarations and stopped-theorem surfaces,
fresh-compiles all targets with `-no-eco`, runs selected upstream baselines,
builds the full paper, rejects undefined references/citations and overfull
boxes, and rechecks source drift.

The final tracked paper-freeze summary is `logs/verify-all-summary.txt`,
SHA-256
`08ef9639dc73d56dba42d02999d07897d29bc8e60aa100a648e9437fd64387ad`.
The pre-freeze 82/82 summary is preserved locally as
`logs/verify-all-before-paper-freeze.log`, SHA-256
`4cd64e5a656be82710bca1410c4d19403a3c661d6b91b0319a0ea8f7c91646da`.

## Trusted computing base

Logical checking relies on the EasyCrypt kernel/type checker and standard
libraries, Why3, and the invoked SMT prover.  Implementation linkage also
trusts the Jasmin parser/compiler and `jasmin2ec` translation, while pinned
source and generated-artifact hashes detect drift but do not prove translator
soundness.  The host shell, filesystem, SHA-256 tool, and LaTeX toolchain are
reproduction/presentation infrastructure.  None of the missing NTT/CRT,
challenge, termination, distribution, or composition leaves is admitted as a
trusted axiom.
