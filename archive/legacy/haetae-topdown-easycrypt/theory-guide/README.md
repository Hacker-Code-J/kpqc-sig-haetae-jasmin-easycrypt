# HAETAE-2 Theory Guide

Separate from the weekly research and development records in `../latex/`,
this directory contains an English translation of the LaTeX guide organized to
help mathematicians and cryptographers understand the verified scope and
remaining obligations.

Read the document around the following topics.

- Partial correctness of the 992-byte packed-key prefix in mode-2 KeyGen;
- the Sign/Verify key-memory relation constructed from that prefix;
- preservation of 992/1408 bytes by the actual public KeyGen/Sign/Verify copy helpers;
- sequential exports and integer/64-bit address bindings of actual raw KeyGen;
- the actual raw Sign exact trace, the successful Verify tail, and hash-input binding;
- the frame condition preserving VK/SK/pre/message across actual Sign's
  1474-byte output and length writes;
- region-local equivalence of actual generated hashes and the sequential Sign→Verify trace;
- 64/32-byte prefix equivalence of the actual generated raw/internal \(\mu\) procedures;
- local zero-loss composition through absorption of the actual challenge \(\mu_{32}\) suffix;
- the actual mode-2 signature's 1056-byte prefix-codec round trip;
- actual HBZ prepare/apply leaf inverses and tail frames;
- actual 13-symbol HBZ table certificates and pure rANS step inverses;
- the common rANS `xs/cuts/bytes` trace, 0/1/2-byte normalization, and state ranges;
- actual encoded-suffix copying and harness control that branches on the encoder result;
- Week 10's array/list suffix connection, actual word steps, internal byte/frame
  invariants, final serialization leaf theorems, and actual successful size bounds;
- Week 11's tail-aware invariant, generated word-step bridge, one-symbol outer
  transition, final serialization composition, and refinement of the actual
  encoder's complete suffix;
- Week 12's decoder cursor, actual table word step, 0/1/2-byte replay, outer/inner
  loop invariants, and exact-trace refinement of the actual decoder;
- Week 13's actual encoder→copy→decoder core inverse, pointwise transport of the
  copied trace to decoder input, decoder-state construction, and W64 size no-wrap bridge;
- Week 14's actual complete HBZ encoder/decoder, exact equivalence at the
  production SignaturePack/Unpack boundaries, and success-conditioned wrapper inverse;
- Week 15's actual all-zero HBZ→all-6 symbol connection, 1020-byte normalization
  budget, exclusion of actual encoder failure, and production fixed-input round trip;
- Week 16's actual `_kp_m23_matrix`→`_keypair_finalize_m23` snapshot composition,
  KG-2-style low/high decomposition, and snapshot-scoped mod-`2q` equality;
- the `output_row` full-invNTT/pointwise representation rewrite compiled as target
  77 in the Week 16 KG-NTT-MUL audit, its two actual row consequences, and the
  `STOP-KG-NTT` decision;
- the direct actual three-helper calls compiled as target 78 in the Week 16 Sign
  pass, accepted-branch control, and the `STOP-SIGN-CHAL-MODE2` decision;
- the actual five-helper sequence added in the Week 16 Verify pass, V-1/V-2/V-5/V-6
  machine-word reconstruction formulas, the W64 norm gate and tail/mismatch word
  expressions, and the `STOP-VERIFY-MATRIX-CRT` decision;
- the `PAPER-FROZEN` boundary aligning these 82 targets with the paper PDF,
  claim matrix, and reproduction procedure;
- odd-root/full-NTT spectral action, mathematical 2-by-3/2-by-4 row products,
  and preservation of representation from `Rq.poly` to `HAETAE_Algebra.poly`,
  closed after paper freeze;
- auxiliary proofs connecting the actual mode-2 `avec` SHAKE128/LE16/rejection
  semantics to the paper's `a`, and composing an independent paper `qj` with
  the finalizer snapshot;
- the latest `STOP-KG-AVEC-QJ — OBL-KG-SECURITY-EXPANDVECA-SEMANTICS` decision,
  which fixes through compiled counterexamples that the existing security
  model's synthetic `haetae_mode23_qj_vector` differs from actual expansion and
  the paper's `qj`;
- remaining fixed-input termination/losslessness, semantic alignment of the
  security model's ExpandVecA, procedure-level Verify matrix/CRT, and the deferred hint (h) codec;
- the stored-observation \(\mu\) edge frozen as product/replay, and remaining
  signature-suffix, context, highbits/LSB, and EUF-CMA obligations.

The operational source of truth for the frozen paper state is
`../CLAIM_LEDGER.md` and `../manifests/paper-artifacts.md`; the ultimate evidence
is the named EasyCrypt declarations. Post-freeze auxiliary results are recorded
separately in `../POST_FREEZE_KG_RQ_HAETAE_REPORT.md` and
`../POST_FREEZE_KG_ACTUAL_AVEC_QJ_REPORT.md`, without retroactively changing the
frozen claim matrix. The frozen manifest remains at 82 authored targets,
including `Mode2SignAcceptedCore.ec` and `Mode2VerifyCoreSequence.ec`.
The completed 78/78 log from before the Verify changes is preserved in
`../logs/verify-all-before-week16-verify.log`, with hash
`cf8056712327dc8211cf93ae427ac5053e8a9d2366747f171392468ac3ff0d75`.
The target-77 KeyGen boundary is recorded in `../WEEK16_KG_NTT_MUL_REPORT.md`,
the target-78 Sign control boundary in `../WEEK16_SIGN_REPORT.md`, and the
82-target Verify partial boundary in `../WEEK16_VERIFY_REPORT.md`. The 82/82
log immediately before paper freeze is preserved in
`../logs/verify-all-before-paper-freeze.log`, with SHA-256
`4cd64e5a656be82710bca1410c4d19403a3c661d6b91b0319a0ea8f7c91646da`.
The 82-target aggregate summary tracked at baseline commit `e87bcc3` is
`../logs/verify-all-summary.txt`; it retains terminal `RESULT PASS`, including
the paper-freeze audit, and SHA-256
`08ef9639dc73d56dba42d02999d07897d29bc8e60aa100a648e9437fd64387ad`.
The frozen paper PDF has SHA-256
`be935948028829556951863b44ceb2e6c5b2037820991b3a43a4b461b036e53d`.

Week 15's `actual_rans_encode_all_six_success` and
`signature_pack_unpack_hbz_zero_success_mode2` show that terminating actual
executions on fixed all-6/all-zero inputs must succeed. These are Hoare
partial-correctness results: they do not prove actual termination, losslessness,
probability-1 success, or nonvacuous execution. The frozen paper decision is
`PAPER-FROZEN`, with internal Verify stopping point `STOP-VERIFY-MATRIX-CRT`.
The Verify side has only partial theorems for canonical decoded \((x,v,h,c)\)
and identified remaining blockers.
`actual_m23_matrix_finalize_semantic_snapshot` closes the snapshot semantics of
two actual KeyGen helpers. In target 77, `output_row_from_mode2_ntt_words` and
`actual_m23_matrix_snapshot_rows_explicit` compile the final frozen rewrite and
the two active-row consequences of the direct two-call harness. After paper
freeze, `rq_mul_coeff_foldr_to_bigi`, full-NTT spectral action, native Rq row
products, and `RqHAETAEBridge.rq_poly_dot3_repr` were closed. The actual `avec`
was also proved to represent the paper's `a` through SHAKE128 with nonces
515/516, little-endian 16-bit parsing, and `<64513` rejection. However, the
existing security object is a synthetic generator whose first coefficient is
401, distinct from the paper's `qj[0][0]=64513` and the actual first coefficient
44985 for the all-zero seed. The latest auxiliary frontier is therefore
`STOP-KG-AVEC-QJ`; full KG-1--KG-4 or `A s = q j (mod 2q)` is not claimed.
On the Verify side, the pure NTT foundation is closed, but the actual 2-by-4
procedure theorems `verify_matrix_ntt_acc_mode2_cols4_correct` and
`verify_crt_freeze_mode2_word_exact` still block the combined matrix theorem.

## Terminology

The original Korean edition introduced explanatory terms in Korean followed by
English in parentheses, then preferred Korean for repeated uses in the same
context. This English edition uses the corresponding English terms. EasyCrypt
theorem and procedure names, claim identifiers, filenames, code snippets, and
standard abbreviations such as `rANS`, `HBZ`, `W32`, `W64`, and `EUF-CMA` remain
unchanged for exact lookup and comparison with the sources. Chapter 1 records
the terminology convention and its examples.

## Build

The historical build command, run from the original workspace root, was:

```sh
sh haetae-topdown-easycrypt/theory-guide/build.sh
```

That historical top-level path is not present at the current repository root.
Build the self-contained English guide in the archived directory with:

```sh
cd archive/legacy/haetae-topdown-easycrypt/theory-guide
latexmk -xelatex -interaction=nonstopmode -halt-on-error main.tex
```

XeLaTeX, `latexmk`, and the TeX Gyre/Latin Modern fonts selected in the preamble
are required. A successful build produces `main.pdf`. The historical build
script also rejected undefined references/citations; for the direct command,
inspect the final log and confirm that none remain.

The original workspace separately verified proofs and documentation with the
following historical command; it is not a command at the current repository root.

```sh
./haetae-topdown-easycrypt/scripts/verify-all.sh
```

A successful guide build does not replace successful EasyCrypt verification.
Consult `../WEEK16_SIGN_REPORT.md`, `../WEEK16_VERIFY_REPORT.md`,
`../WEEK16_KG_NTT_MUL_REPORT.md`, `../manifests/paper-artifacts.md`, the two
`../POST_FREEZE_KG_*.md` reports, and preserved logs for verification decisions.
The Week 14 and Week 13 records are historical cross-checks of the underlying
full-HBZ and rANS core boundaries, respectively. Use
`../logs/verify-all-summary.txt` as current aggregate evidence only after
checking both terminal `RESULT PASS` and its hash. The pre-Verify-change 78/78
completed log is preserved in `../logs/verify-all-before-week16-verify.log`,
with hash `cf8056712327dc8211cf93ae427ac5053e8a9d2366747f171392468ac3ff0d75`.
The 82/82 `-no-eco` aggregate immediately before paper freeze is preserved in
`../logs/verify-all-before-paper-freeze.log`, with the `4cd64...` hash above.
The baseline commit's frozen-suite summary retains the `08ef96...` hash. The
three post-freeze `KgActualAvecQj*.ec` targets are auxiliary proofs outside the
frozen 82-target manifest; consult the latest post-freeze reports separately
for their individual fresh-compilation evidence and deterministic traces.
