# HAETAE top-down EasyCrypt sprints

This directory is an isolated, mode-2-first proof workspace. It records what
is fresh-compiled about the pinned HAETAE Jasmin implementation, what is only
specified, and which named obligations still block a public-API EUF-CMA
theorem. The LaTeX document is a research-development narrative; this
Markdown tree and the generated verification logs are the operational source
of truth.

## Reader guides

- `algebraist-guide/`: 순수 대수학자와 대수기하학자를 위한 한국어 동반
  안내서. 몫환·모듈에서 바이트 표현과 실제 상태기계 refinement까지의 번역에
  집중한다.
- `theory-guide/`: 수학자와 암호이론가를 위한 상세한 현재 증명 현황서.
- `latex/`: 주차별 연구개발 기록과 검증 결과.

대수학자용 안내서는 저장소 루트에서 다음과 같이 빌드한다.

```sh
sh haetae-topdown-easycrypt/algebraist-guide/build.sh
```

## Reproduce

From the repository root:

```sh
./haetae-topdown-easycrypt/scripts/verify-all.sh
```

The verifier:

- checks pinned source hashes and tracked read-only-tree drift;
- regenerates the focused packer, mu-hash, transcript, API copy-helper,
  actual raw-ABI caller, signature-codec, HBZ/rANS, Sign accepted-core, and
  Verify-core extractions;
- checks the regenerated targets against
  `manifests/generated-extractions.sha256`;
- regenerates the concrete HBZ symbol-table certificate and checks its
  pinned generator/output hashes;
- compiles every manifested authored EasyCrypt target with `-no-eco`;
- scans for proof holes, authored axioms, and debug declarations;
- checks target-manifest completeness;
- fresh-compiles selected upstream baselines; and
- builds `latex/main.pdf` and rejects undefined references/citations.

The Week 12 pre-edit baseline is preserved in
`logs/verify-all-before-week12.log` (all earlier historical baselines remain
unchanged), and the Week 14 pre-edit 67-target baseline is preserved in
`logs/verify-all-before-week14.log`. The pre-edit Week 16 baseline reports 74
authored `-no-eco` targets and is preserved in
`logs/verify-all-before-week16.log` (SHA-256
`da7a7516166d54e93665d36e9a81348050ac6a83786111eb83ac6901743d6056`).
The KG-NTT-MUL continuation baseline is the fresh 76-target run preserved in
`logs/verify-all-before-kg-ntt-mul.log` (SHA-256
`c556834b6e881930c8357ed136c5eb138a1a63bfdb977f194a63edae3298f348`).
The 77-target pre-Sign baseline is preserved in
`logs/verify-all-before-week16-sign.log` (SHA-256
`8480d2e2f2ddda421c3d244ab5ec0a50196cadd7a8e1a29e996fd307aec7db57`).
The pre-Verify manifest contains 78 authored targets, ending at the focused
Sign accepted-core control boundary. That baseline aggregate is preserved in
`logs/verify-all-before-week16-verify.log` (exactly 78 fresh compiles, terminal
`RESULT PASS authored-targets=78 cache=-no-eco`, SHA-256
`cf8056712327dc8211cf93ae427ac5053e8a9d2366747f171392468ac3ff0d75`).
The current manifest contains 82 targets after adding the four focused Verify
theories. The completed aggregate is preserved in
`logs/verify-all-week16-verify-matrix-crt.log` (exactly 82 fresh compiles, one terminal
`RESULT PASS authored-targets=82 cache=-no-eco`, SHA-256
`4cd64e5a656be82710bca1410c4d19403a3c661d6b91b0319a0ea8f7c91646da`).

Detailed logs are written only under `logs/`. A pre-existing Why3 server can be
reused with `WHY3_SERVER_SOCKET=/path/to/socket`; otherwise the verifier starts
and cleans up a private one.

The individual reproduction surfaces are:

```sh
./haetae-topdown-easycrypt/scripts/extract-packers.sh
./haetae-topdown-easycrypt/scripts/extract-mu-hash.sh
./haetae-topdown-easycrypt/scripts/extract-transcripts.sh
./haetae-topdown-easycrypt/scripts/extract-api-key-memory.sh
./haetae-topdown-easycrypt/scripts/extract-raw-api-callers.sh
./haetae-topdown-easycrypt/scripts/extract-signature-codec.sh
./haetae-topdown-easycrypt/scripts/extract-hbz-codec.sh
./haetae-topdown-easycrypt/scripts/extract-sign-accepted-core.sh
./haetae-topdown-easycrypt/scripts/extract-verify-core.sh
./haetae-topdown-easycrypt/scripts/generate-hbz-symbol-certificate.sh
./haetae-topdown-easycrypt/scripts/verify-baselines.sh
./haetae-topdown-easycrypt/scripts/build-notes.sh
```

Toolchain observed on 2026-08-05:

- Jasmin compiler / `jasmin2ec`: 2026.03.0;
- EasyCrypt: OPAM switch `easycrypt-5.2`, configured git hash `n/a`;
- Why3: 1.8.0;
- configured provers: Alt-Ergo 2.6.0, CVC4 1.8.0, CVC5 1.2.1, Z3 4.12.6.

## Week 3 checked claims

The packed-key seam is now procedure-level partial correctness:

- `ExtractedPackedKeyPrefix.pack_sk_m23_mode2_vk_prefix` proves that the
  generated `_pack_sk_m23` result has the same first 992 bytes as its input VK
  under the concrete mode-2 parameters.
- `pack_vec_eta_to_prefix_frame` and `pack_vec2_eta_to_prefix_frame` prove that
  subsequent eta-vector writes do not change `[0,992)`.
- `keypair_full_m23_mode2_return_prefix` and
  `keypair_internal_mode2_return_prefix` lift the property to the generated
  `_keypair_full_m23` and mode-2 internal KeyGen entry.

These are Hoare partial-correctness theorems: they say what holds if a call
returns. They neither assume nor prove retry termination, losslessness, or the
paper KeyGen distribution.

The raw/internal mu path is proved through the actual generated helper chain:

- `sign_sk_verify_vk_absorb_mode2` relates Sign's packed-SK absorb to Verify's
  raw-memory VK absorb for 992 equal bytes.
- `sign_verify_absorb_addr_from_same_state`,
  `sign_verify_finalize_from_same_state`, and
  `sign_verify_keccakf1600_from_same_state` connect the identical pre/message,
  finalize, and Keccak paths.
- `sign_verify_final_squeeze_mu32_prefix` proves that Sign's generated
  64-byte squeeze and Verify's generated 32-byte squeeze agree on bytes
  `[0,32)`.
- `sign_verify_raw_mu_core_prefix` and
  `sign_verify_raw_mu_top_wrappers_prefix` compose those facts into
  `take_32(mu_sign^64) = mu_verify^32` for the explicit raw wrappers.

Week 3 closes the generated top-level control boundary:

- `sf_mu_rawpre_refines_raw_top` relates the actual generated
  `SignMuHashTarget.M._sf_mu_rawpre` to the proved raw Sign wrapper, including
  generated stack/state initialization, erased scheduling operations,
  `protect_ptr`, and the 64-byte squeeze.
- `verify_hash_mu_raw_refines_raw_top` proves that `raw_prelen` forces the
  actual generated `VerifyMuHashTarget.M.__verify_hash_mu` into its raw branch
  and relates that execution to the raw Verify wrapper.
- `sign_verify_generated_raw_mu_prefix` has the two actual generated
  procedures on the two sides of its `equiv` statement and proves
  `take_32(mu_sign^64) = mu_verify^32` under explicit mode-2, memory, address,
  length, raw-branch, and no-wrap premises.
- `generated_raw_mu_to_challenge_suffix_zero_loss` invokes those actual hash
  procedures followed by the actual generated mu32 challenge-absorb helpers
  and proves equal returned challenge state and position from position 64.

`keypair_internal_return_reaches_generated_raw_mu_preconditions` consumes the
Hoare theorem for the actual generated mode-2 internal KeyGen return and
constructs a concrete Verify memory image together with raw/no-wrap premises.
This closes reachability for the local-array/raw path, not yet public API
pointer marshalling.

The Week 3 secondary API work also reaches actual generated copy helpers:

- `keygen_export_vk_mode2_prefix` proves that
  `__kp_api_copy_2080_to_addr` exports the first 992 VK bytes;
- `keygen_export_sk_mode2_prefix` proves that
  `__kp_api_copy_2752_to_addr` exports all 1408 mode-2 SK bytes;
- `keygen_export_sk_mode2_prefix_frames_vk` additionally proves that this SK
  write preserves a disjoint previously exported 992-byte VK region;
- `sign_import_mode2_sk_prefix` and `verify_import_mode2_vk_prefix` prove the
  corresponding actual generated 1408/992-byte raw imports; and
- `imported_sign_sk_reaches_mu_memory` connects imported prefix equality to
  the `sk_memory_prefix` premise used by the generated mu theorem.

These are procedure-level partial-correctness results over explicit
`valid_region_w64` or `valid_region_int` premises. The full sequential public
API chain remains **PARTIAL**: it still needs to compose the two exporter
calls at the real caller, establish the caller-level `W64.to_uint`/`int`
pointer binding, and discharge public-call ownership/alias orchestration.

## Exact boundary

`KG-PREFIX-CALL` is **PROVED as partial correctness** and
`OBL-MU-TOPLEVEL-CONTROL` is **PROVED** for the raw/internal path. Therefore
the local generated top-level seam has `delta_mu_raw_top = 0`. The result does
not prove complete public API marshalling, the context branch, highbits/LSB equality,
or any complete `delta_Sign`, `delta_Verify`, or `delta_Encoding` bound.

The public-context path (`_sf_prepare_pre_raw + _sf_mu_preptr` and Verify's
high-bit branch) remains **SPECIFIED**. No result here implies that full
`delta_Sign`, `delta_Verify`, or `delta_Encoding` is zero.

See `WEEK1_REPORT.md`, `WEEK2_REPORT.md`, `WEEK3_REPORT.md`,
`WEEK4_REPORT.md`, `WEEK5_REPORT.md`, `CLAIM_LEDGER.md`, and
`THEOREM_GRAPH.md` for the measured boundary.

## Week 4 raw-ABI result

Week 4 proves `OBL-API-ADDRESS-BINDING`, exact extraction identity for the raw
Sign/Verify hash procedures, exact actual-to-trace control for the raw KeyGen
and Sign callers, Sign SK-import/hash-input reachability, Verify trace
equivalence through `sign_verify_internal_mode2_jazz`, and a stores-free
external-memory-to-`sk_memory_prefix` bridge.

`OBL-API-KEY-MEMORY-RAW` nevertheless remains **PARTIAL**. The single actual
KeyGen caller Hoare composition of both exports is still a named residual, and
the actual Verify raw/public caller can reject before reaching
`_sign_verify_tail_m23`. Therefore `delta_mu_raw_api = 0` is not claimed and
highbits/LSB work remains gated. See `WEEK4_REPORT.md` for the theorem premises,
alias matrix, failed proof decompositions, and Week 5 decision.

## Week 5 accepted-path result

Week 5 preserves the Week 4 statement above as a historical boundary and
closes two of its concrete residuals:

- `keypair_raw_api_exports_matching_prefixes` is a Hoare theorem over the
  actual `cryptolab_haetae_mode2_keypair_internal` procedure.  Every returning
  execution satisfying the seed/read, canonical-region, and disjoint-output
  contracts leaves equal bytes in the external SK and VK regions for all
  offsets `[0,992)`.  It does not assert KeyGen termination.
- `verify_raw_api_exact_mu_trace` and
  `verify_cryptolab_exact_mu_trace` preserve the actual Verify result and
  final `Glob.mem` on every early-reject and tail branch.
- `verify_raw_api_actual_accept_implies_trace_tail_reached` and
  `verify_cryptolab_actual_accept_implies_trace_tail_reached` prove the
  security-facing direction `accept => tail_reached`; neither valid signature
  length nor an arbitrary signature is claimed to reach the tail.
- `verify_raw_api_actual_accept_binds_hash_inputs` and its cryptolab lift bind
  accepted executions to the concrete VK/pre/message descriptor values used
  at the actual `__verify_hash_mu` call.
- `raw_api_accepting_execution_hash_mu_zero_loss` and
  `raw_api_accepting_execution_generated_challenge_suffix_zero_loss` compose
  those trace facts with the already proved generated hash and position-64
  absorb relations.

The old parent `OBL-API-KEY-MEMORY-RAW` is now explicitly split.  Its
security-facing child `OBL-API-KEY-MEMORY-RAW-ACCEPT` remains **PARTIAL**:
there is not yet one compiled theorem comparing
`SignRawApiMuTrace.observed_mu` with
`VerifyCryptolabMuTrace.observed_mu`. Week 6 does prove the actual Sign output
frame and the region-local generated hash relation, but those facts have not
yet been converted into a post-state relation between two already completed
trace calls. Therefore the project does not claim
`delta_mu_raw_api_accept = 0`; only the accepted trace-bound generated hash
call and helper suffix adapters have zero deterministic loss.

`OBL-SIGN-OUTPUT-TAIL-REACH` is separately **SPECIFIED**, and
`OBL-SIGN-VERIFY-CORRECTNESS` remains **BLOCKED** on pack/unpack, norm, hint,
arithmetic, and challenge correctness.  Highbits/LSB work remains gated until
the direct observed-mu edge is closed.

## Week 6 frame/locality result

Week 6 adds three fresh-compiled theory targets.

- `RawApiSignOutputFrame.sign_raw_api_frames_reused_regions` opens the actual
  `cryptolab_haetae_mode2_signature_internal` path through its exact trace and
  proves that the 1474-byte signature copy followed by the 8-byte siglen store
  preserves disjoint VK/SK/pre/message regions. It is partial correctness and
  does not assert rejection-loop termination.
- `RegionLocalMuTop.sign_verify_generated_raw_mu_prefix_regionwise` directly
  compares the actual generated `_sf_mu_rawpre` and `__verify_hash_mu` while
  permitting different global memories. Only the key, pre, and message bytes
  actually read by the hash calls are related.
- `RawApiDirectObservedMu.raw_sign_then_verify_actual_exact_trace` executes the
  actual raw Sign then actual raw Verify sequence on one side and the two exact
  trace procedures on the other, preserving results and final memory.
  `sign_then_verify_trace_accept_implies_tail_reached` and
  `sign_then_verify_accept_binds_observed_inputs` derive control and inputs
  from post-state execution, without observation fields in their premises.

The remaining blocker is deliberately narrow but substantive: there is no
compiled product/replay argument turning the region-local pRHL result for two
hash calls into
`mu32_prefix(SignRawApiMuTrace.observed_mu,
VerifyCryptolabMuTrace.observed_mu)` after both calls have already executed.
This keeps `OBL-DIRECT-OBSERVED-MU` and its parent **PARTIAL**.

## Week 7

Week 7 is a decision sprint, not a scope-expansion sprint.

- `PRODUCT_REPLAY_DECISION.md` records the explicit time-boxed decision on
  `OBL-MU-PRODUCT-REPLAY`. The current result is a paper-boundary freeze, not
  a claimed `delta_mu_raw_api_accept = 0`.
- `SIGNATURE_CODEC_OBLIGATIONS.md` records the new mode-2 signature
  pack/unpack extraction hashes, audited wrapper constants, verified 1474-byte
  layout, and staged codec obligations.
- `easycrypt/refinement/sign/Mode2SignaturePrefixCodec.ec` pins the exact
  mode-2 constants, canonical input predicates, bit/sign-extension lemmas, and
  a concrete non-vacuity witness.
- `Mode2SignaturePrefixPack.ec` and `Mode2SignaturePrefixUnpack.ec` open the
  actual generated `_pack_sig_prefix` and `_unpack_sig_prefix` loops.
  `Mode2SignaturePrefixRoundTrip.ec` calls those two procedures sequentially;
  `pack_unpack_sig_prefix_mode2_roundtrip` proves recovery of all 256 challenge
  bits and 1024 signed low words on canonical inputs. This is partial
  correctness, not Sign termination.
- `OBL-SIG-PREFIX-CODEC` is therefore **PROVED** within that boundary.
  Metadata, zero padding, both suffix rANS inverses, residual array frames,
  full canonical parsing, and Sign-output tail reach remain open. Week 8 begins
  with `OBL-SIG-HBZ-ENCODE-DECODE`.

## Week 8

Week 8 keeps the Week 7 product/replay freeze unchanged and moves only along
`OBL-SIG-HBZ-ENCODE-DECODE`.

- `Mode2HbzPrepare`, `Mode2HbzApply`, and `Mode2HbzLeafRoundTrip` close the
  actual mode-2 HBZ coefficient↔symbol leaf layer and its local tail frames.
- `Mode2HbzActualBoundary` proves that the focused Week 8 HBZ extraction and
  the Week 7 signature pack/unpack extraction expose the same actual
  `_encode_hb_z1_full` / `_decode_hb_z1_full` procedures.
- `Mode2HbzTableCertificate` together with
  `Mode2HbzSymbolWordsGenerated.actual_mode2_hbz_tables_certified` closes the
  concrete mode-2 arithmetic/table certificate.
- `Mode2RansCore` proves the pure quotient/slot inverse and connects the
  concrete reciprocal fast step to that mathematical inverse on its explicit
  normalized-state range.

The parent claim `OBL-SIG-HBZ-ENCODE-DECODE` nevertheless remains
**PARTIAL**.  The actual encoder and decoder normalization loops have not yet
been refined to the pure byte-stack model; consequently the actual core
inverse, the success-conditioned full-wrapper composition, and an actual
successful witness remain open.  Week 9 therefore stays on
`CONTINUE-RANS` and does not move to the `h` codec.

## Week 9

Week 9 implements the shared reverse-encode/forward-decode trace and recovers
the actual suffix-copy theorem, but it does not overstate the remaining loop
refinement.

- `Mode2RansByteStack.ec` defines `xs/cuts/bytes`, the 0/1/2 normalization
  segments, little-endian state serialization, and proves pure readback plus
  mode-2 state-bound preservation.
- `Mode2RansNormalization.ec` proves the actual W32 shift/truncate/append byte
  order and W64 cursor-decrement facts used by the nested loops.
- `Mode2RansSuffixCopy.copy_encoded_suffix_correct` directly opens actual
  `__copy_encoded_suffix` and proves exact slice copy plus output-tail frame.
- `Mode2RansEncodeRefinement` and `Mode2RansDecodeRefinement` contain direct
  generated-procedure control theorems. They fix concrete mode-2 tables and
  return-state fields, but do not yet prove trace refinement.
- `Mode2RansActualHarness.run` directly executes actual `_rans_encode`, the
  actual suffix copy on the returned `off/size`, and actual `_rans_decode`.
  `actual_rans_harness_branches_on_encoder_result` proves that the decoder is
  reached exactly on the actual encoder-success branch and receives
  `(count,size,m)=(1024,size,13)`.

The actual encoder-to-trace and trace-to-decoder outer-loop invariants remain
open. Therefore `OBL-RANS-CORE-INVERSE`, the successful actual witness, and
`OBL-SIG-HBZ-ENCODE-DECODE` remain **PARTIAL**. No decoder success, symbol
round trip, final state `2^23`, consumed-size equality, canonical parsing,
encoding zero-loss, or security result is claimed. Week 10 remains
`CONTINUE-RANS`; the `h` codec stays out of scope.

## Week 10

Week 10 stays encoder-only and adds six fresh-compiled theories.

- `Mode2RansArrayListBridge` relates the actual BArray symbol prefix to a
  1024-element list, proves suffix recurrence/canonicality, and supplies
  reusable byte-segment and prefix-frame algebra.
- `Mode2RansEncoderWordStep` proves the exact concrete mode-2 reciprocal/table
  arithmetic operation equals the pure fast encoder step on its normalized
  range.
- `Mode2RansEncoderInnerProgress` proves the pure 0/1/2-byte progress and exact
  prepend update for `segment_matches`.
- `Mode2RansEncoderSerialization` proves the final four little-endian writes,
  outside-byte frame, and scalar success-size arithmetic.
- `Mode2RansEncoderTrace` provides the phase/segment predicates and compiled
  one-step preservation lemmas used by the generated loop proof.
- `Mode2RansEncoderActualInner` directly proves the actual generated
  `_rans_encode`. Its nested normalization loop maintains the actual `set8`
  byte segment and prefix frame with W64 no-underflow. Its success corollary
  proves `0 <= returned_off <= 1020` and
  `4 <= 1024-returned_off <= 1024`, while preserving the failure disjunct.

This is stronger implementation evidence than the Week 9 control theorem, but
`OBL-RANS-ENCODE-REFINEMENT` remains **PARTIAL**: no compiled postcondition yet
equates the entire returned suffix with
`trace_bytes(symbol_list_of_array(symbols0))`.  The missing edge is the actual
outer one-symbol transition through generated table loads, protect erasures,
reciprocal update, and the pure suffix recurrence, followed by composition of
the actual final stores.  No actual success/termination witness exists.

The Week 11 decision is **CONTINUE-ENCODER**. Decoder semantic refinement and
all wider codec/security lanes remain out of scope until that exact actual
encoder suffix theorem compiles.

## Week 11

Week 11 closes that encoder-only edge without adding a procedure wrapper.
`Mode2RansEncoderActualTraceClosure.actual_rans_encode_trace_closure` is a
Hoare theorem over the generated `RansEncodeTarget.M._rans_encode` itself. It
branches on the procedure's returned `bad`; on success it proves:

```text
segment_matches(
  returned_encp,
  uint(returned_off),
  trace_bytes(symbol_list_of_array(symbols0)))

uint(returned_off) +
  size(trace_bytes(symbol_list_of_array(symbols0))) = 1024
```

It also proves `0 <= uint(returned_off) <= 1020`, encoded size in `[4,1024]`,
and a frame from the initial encoder array below the returned offset.
`actual_rans_encode_trace_refinement` exposes the same result as the public
Week 11 corollary. Both fresh-compile with `-no-eco`.

The proof carries `normalization_bytes ++ encode_trace(tail).bytes` through
the actual nested normalization loop, uses the concrete generated table-load
and reciprocal word update, re-establishes the outer invariant for one actual
symbol, and composes the generated four-byte final-state stores. Therefore
`OBL-RANS-ENCODE-REFINEMENT` is **PROVED as success-conditioned partial
correctness**.

This result does not prove encoder termination or reachability of the success
branch. `OBL-RANS-ACTUAL-SUCCESS-WITNESS`, actual decoder refinement, the rANS
core inverse, and the full HBZ codec remain `PARTIAL`. The Week 12 decision is
**GO-ENCODER**: proceed only to actual decoder trace refinement.

## Week 12

Week 12 closes the decoder semantic edge at the generated-procedure level.
The direct theorem
`Mode2RansDecoderTopHoare.actual_rans_decode_trace_refinement` targets
`RansDecodeTarget.M._rans_decode`. Given a canonical 1024-symbol array, an
encoded buffer containing exactly its `trace_bytes`, size in `[4,1024]`, state
fields `(count,size,m)=(1024,encoded_size,13)`, and the literal mode-2 decode
tables, every terminating execution satisfies:

```text
returned bad = 0
returned offset = encoded_size
decoded[0..1024) = expected_symbols[0..1024)
decoded[1024..2048) = decoded_initial[1024..2048)
```

The proof parses the actual little-endian state, connects generated packed
table loads and W32 arithmetic to the concrete decoder step, consumes each
0/1/2-byte normalization segment in the actual nested loop, and obtains
internal `x=2^23` plus `off=encoded_size` at outer-loop exit. It then proves
that both generated final reject checks are bypassed. No decoder wrapper,
table axiom, output-equality premise, or arbitrary buffer witness is used.

This is Hoare partial correctness, not a losslessness or termination result.
It also does not establish that the actual encoder reaches its success branch.
`OBL-RANS-DECODE-REFINEMENT` is now **PROVED (exact-trace partial
correctness)**, while `OBL-RANS-CORE-INVERSE` stays **PARTIAL** until the
existing actual encoder theorem and actual suffix-copy theorem are composed
with this decoder theorem in the unary harness. The Week 13 decision is
**GO-DECODER** with that single composition edge; the `h` codec, full HBZ
wrapper, metadata, and security lanes remain out of scope.

## Week 13

Week 13 closes the actual rANS core composition edge. The new theorem
`Mode2RansCoreActualInverse.actual_rans_encode_copy_decode_inverse` is a Hoare
theorem over the existing `Mode2RansActualHarness.run`, whose execution path
directly contains:

```text
RansEncodeTarget.M._rans_encode
  -> HbzFullEncodeTarget.M.__copy_encoded_suffix
  -> RansDecodeTarget.M._rans_decode
```

The theorem requires only exact initial argument binding and a canonical
mode-2 1024-symbol stream. It does not require encoder success. The actual
returned `bad` selects one of two proved outcomes:

- failure: the decoder is not run and the initial decoded array/state are
  retained;
- success: the actual copied buffer supplies the exact decoder trace, the
  decoder returns `bad=0`, consumes exactly the encoded size, recovers all
  1024 symbols, and preserves `[1024,2048)` of the decoded array.

`Mode2RansCoreCompositionBridge` supplies the non-assumptive adapter chain:
encoder `segment_matches` plus actual copy `slice_eq` gives copied
`segment_matches`; that global relation implies every Week 12 pointwise
decoder read; the harness's three actual state stores establish
`(count,size,m)=(1024,size,13)`. A separate W64/int lemma proves that
`W64.of_int 1024 - encoder_off` is the exact trace length under the actual
success bounds, with no modular wraparound.

Accordingly `OBL-RANS-CORE-INVERSE` is **PROVED as success-conditioned partial
correctness**. The Week 13 theorem by itself does not prove encoder success
reachability, encoder or
decoder termination, the production full-HBZ wrapper inverse, canonical
malformed-input rejection, or any encoding/security zero-loss claim.
`OBL-RANS-ACTUAL-SUCCESS-WITNESS` is now **PROVED (fixed all-6 input, Hoare
partial correctness)**. Week 15 records that witness only.  Its original
Week 16 `h`-codec recommendation was later superseded by the narrower KeyGen
snapshot leaf.

## Week 14

Week 14 closes the production full-HBZ wrapper boundary. The exact theorem
`Mode2HbzSignatureBoundaryLift.signature_pack_unpack_hbz_full_actual_exact`
proves that the production SignaturePack/Unpack harness and the focused
full-HBZ harness expose the same buffers and decoder-reachability flag. The
Hoare corollary `signature_pack_unpack_hbz_full_inverse_mode2` keeps the same
failure/success split on the public pack/unpack route.

The production boundary remains success-conditioned:

- failure: `size = 0`, `decoder_ran = false`, and the initialized encoded,
  decoded, and `bad` values are preserved;
- success: `size <> 0`, `4 <= size <= 1024`, `decoder_ran = true`,
  `bad = 0`, `decoded_hbz_prefix`, `coeff_tail_frame`, `suffix_frame`, and a
  concrete `prepared_symbols` witness whose trace bytes match the returned
  encoded buffer.

This is the production formal lift. It closes the wrapper composition, but it
does not prove encoder-success reachability for arbitrary inputs. The fixed
all-6 success witness now compiles separately.  The `h` codec remains outside
the active one-week minimum-paper scope.

## Week 15

Week 15 records the fixed all-6 witness only. The exact witness is
`Mode2RansActualSuccessWitness.actual_rans_encode_all_six_success`, and the
fixed-input HBZ lift is carried by
`full_rans_encode_all_six_success`,
`actual_encode_hb_z1_full_zero_success`,
`signature_pack_hbz_zero_success_mode2`,
`actual_hbz_full_encode_decode_zero_success_mode2`, and
`signature_pack_unpack_hbz_zero_success_mode2`. This remains Hoare partial
correctness only: every terminating fixed-input execution returns the stated
success result. It does not add termination, losslessness, probability-one
success, or a non-vacuous execution theorem.

## Week 16 — MINCORE keygen snapshot

The active Week 16 result is narrower than the previous paper target.  The
compiled KeyGen surface is the transparent two-call harness:

- `ActualM23MatrixFinalizeSnapshot.run` calls `_kp_m23_matrix` and
  `_keypair_finalize_m23` in sequence and returns the snapshot needed by the
  later bridge;
- `Mode2KeygenSnapshotAlgebra` proves the residue split, low/high parity
  relation, and the mod-2q snapshot congruence lemmas; and
- `Mode2KeygenCoreEquation.actual_m23_matrix_finalize_semantic_snapshot`
  exports the actual snapshot low/high decomposition and the mod-2q zero
  identity through the two-call harness.

This is a focused keygen leaf, not the paper KeyGen theorem.  The KG-NTT-MUL
continuation reused the checked actual forward-NTT, pointwise, and inverse-NTT
leaves and fresh-compiled `Mode2KeygenNttMulBridge` as the last honest
`output_row` representation rewrite. Its
`actual_m23_matrix_snapshot_rows_explicit` corollary carries that expression
to both rows returned by the direct matrix/finalizer harness without copying
the actual loops. The checked NTT tree still lacks the
odd-root orthogonality/full-NTT convolution identity
`mont(full_invntt(ahat * full_ntt(p) * inv R)) = full_invntt(ahat) &* p`, and
the `Rq.poly`-to-security-list multiplication adapter is also absent.

The final decision is therefore **STOP-KG-NTT**, not `GO-KG`.  KeyGen is
frozen at KG-2/finalization: faithful KG-1, KG-3, complete KG-4, and the paper
`A s = q j (mod 2q)` are not proved.  No sampler, retry, packer, public API,
termination, or security claim is made. `WEEK16_KG_NTT_MUL_REPORT.md` records
the missing leaf at procedure and formula level.

The next Sign pass fresh-compiled `Mode2SignAcceptedCore`, whose transparent
harness calls actual `_sf_round_challenge_mode2`, `_sf_z_check`, and
accepted-only `_sf_hint_mode2` in that order. The checked theorem proves only
the branch-control fact and has precondition `true`. The paper S-1--S-7
theorem is stopped at **STOP-SIGN-CHAL-MODE2**: the exact missing
`sf_challenge_mode2_highbits_lsb_sampleinball_correct` leaf cannot be replaced
by the current abstract `challenge_hash`, which omits highbits. Paper S-1 and
S-4 also retain the frozen full-NTT convolution dependency. Response, norm,
hint, distribution, and termination claims remain open; the active MINCORE
lane then moved to Verify. See `WEEK16_SIGN_REPORT.md`.

The Verify pass fresh-compiles four focused theories over the canonical
decoded-array boundary. `ActualVerifyCoreSequence.run` directly calls the
actual prepare, matrix, recover, norm, and norm-gated tail helpers in order.
Independent theorems preserve exact machine-word V-1, V-2, V-5, and V-6,
the exact W64 norm decision, the tail procedure trace, and the actual
`_poly_mismatch` accumulator/result expression. None assumes `reject=0`, a
reconstruction result, norm acceptance, or challenge equality.

The continuation decision is **STOP-VERIFY-MATRIX-CRT**, not `GO-VERIFY`.
The absent headline `verify_matrix_crt_mode2_fromcrt_freeze_exact` now has an
exact dependency split: `verify_matrix_ntt_acc_mode2_cols4_correct` must
establish the actual 2-by-4 NTT row product, while
`verify_crt_freeze_mode2_word_exact` must establish the two actual parity
lifts and 512-word freeze. The NTT side first lacks
`rq_mul_coeff_foldr_to_bigi` and then the full-NTT Montgomery spectral action.
Consequently paper V-3/V-4 and the full Verify predicate are not claimed.
Paper V-6 also
retains its parity/centering integer bridge, the norm gate retains its
integer/no-wrap bridge, and the challenge path retains
`verify_tail_m23_highbits_lsb_sampleinball_correct`. Parser, malformed input,
codec, public API, KeyGen NTT expansion, Sign blockers, distribution, and
termination remain outside this result. See `WEEK16_VERIFY_REPORT.md`.
